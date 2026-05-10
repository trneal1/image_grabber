#!/usr/bin/env python3
"""
nws_state_alert_display.py

Draw a county-level NWS alert map for one state and send it to the ESP32 TFT
using the same raw RGB565 "RGB!" TCP protocol as iem_radar_display.py.

Sources:
  Counties : U.S. Census TIGERweb State_County GeoJSON
  Alerts   : api.weather.gov active alerts endpoint

Alert county matching uses NWS alert properties.geocode.SAME. SAME codes are
six digits; the last five digits are the county FIPS code used by Census.

Usage:
  python nws_state_alert_display.py --state NC --host 192.168.1.42
  python nws_state_alert_display.py --state NC --host 192.168.1.42 --interval 120
  python nws_state_alert_display.py --state NC --host 192.168.1.42 --rotation 1

Requirements:
  pip install pillow requests
"""

import argparse
import io
import socket
import struct
import sys
import time
from datetime import datetime

try:
    import requests
except ImportError:
    sys.exit("requests is required:  pip install requests")

try:
    from PIL import Image, ImageDraw, ImageFont
except ImportError:
    sys.exit("Pillow is required:  pip install pillow")


DISPLAY_W = 320
DISPLAY_H = 480
TCP_PORT = 5555
MAGIC = b"RGB!"

TIGERWEB_COUNTIES = (
    "https://tigerweb.geo.census.gov/arcgis/rest/services/"
    "TIGERweb/State_County/MapServer/9/query"
)
NWS_ALERTS = "https://api.weather.gov/alerts/active"

STATE_FIPS = {
    "AL": "01", "AK": "02", "AZ": "04", "AR": "05", "CA": "06",
    "CO": "08", "CT": "09", "DE": "10", "DC": "11", "FL": "12",
    "GA": "13", "HI": "15", "ID": "16", "IL": "17", "IN": "18",
    "IA": "19", "KS": "20", "KY": "21", "LA": "22", "ME": "23",
    "MD": "24", "MA": "25", "MI": "26", "MN": "27", "MS": "28",
    "MO": "29", "MT": "30", "NE": "31", "NV": "32", "NH": "33",
    "NJ": "34", "NM": "35", "NY": "36", "NC": "37", "ND": "38",
    "OH": "39", "OK": "40", "OR": "41", "PA": "42", "RI": "44",
    "SC": "45", "SD": "46", "TN": "47", "TX": "48", "UT": "49",
    "VT": "50", "VA": "51", "WA": "53", "WV": "54", "WI": "55",
    "WY": "56", "PR": "72",
}

ALERT_PRIORITIES = {
    "other": 1,
    "statement": 2,
    "advisory": 3,
    "watch": 4,
    "warning": 5,
}

ALERT_COLORS = {
    "none": (31, 38, 48),
    "other": (150, 80, 210),
    "statement": (40, 110, 235),
    "advisory": (42, 170, 84),
    "watch": (245, 214, 55),
    "warning": (225, 38, 38),
}

SESSION = requests.Session()
SESSION.headers.update({
    "User-Agent": "ESP32-StateAlertDisplay/1.0",
    "Accept": "application/geo+json, application/json",
})


def source_size_for_rotation(rotation: int) -> tuple[int, int]:
    if rotation % 2:
        return DISPLAY_H, DISPLAY_W
    return DISPLAY_W, DISPLAY_H


def rotate_image_pixels(img: Image.Image, rotation: int) -> Image.Image:
    rotation %= 4
    if rotation == 0:
        return img.convert("RGB")
    if rotation == 1:
        return img.transpose(Image.Transpose.ROTATE_270).convert("RGB")
    if rotation == 2:
        return img.transpose(Image.Transpose.ROTATE_180).convert("RGB")
    if rotation == 3:
        return img.transpose(Image.Transpose.ROTATE_90).convert("RGB")
    raise ValueError(f"invalid rotation {rotation}")


def classify_alert(event: str) -> str:
    event = event.lower()
    if "warning" in event:
        return "warning"
    if "watch" in event:
        return "watch"
    if "advisory" in event:
        return "advisory"
    if "statement" in event:
        return "statement"
    return "other"


def same_to_county_fips(code: str) -> str | None:
    digits = "".join(ch for ch in str(code) if ch.isdigit())
    if len(digits) < 5:
        return None
    return digits[-5:]


def fetch_counties(state_abbr: str) -> list[dict]:
    state_fips = STATE_FIPS[state_abbr]
    params = {
        "where": f"STATE='{state_fips}'",
        "outFields": "GEOID,NAME,BASENAME,STATE",
        "returnGeometry": "true",
        "outSR": "4326",
        "f": "geojson",
    }
    r = SESSION.get(TIGERWEB_COUNTIES, params=params, timeout=30)
    r.raise_for_status()
    data = r.json()
    features = data.get("features", [])
    if not features:
        raise RuntimeError(f"No Census counties returned for {state_abbr}")
    return features


def fetch_alert_levels(state_abbr: str) -> dict[str, str]:
    params = {"area": state_abbr}
    r = SESSION.get(NWS_ALERTS, params=params, timeout=30)
    r.raise_for_status()
    data = r.json()

    county_levels: dict[str, str] = {}
    for feature in data.get("features", []):
        props = feature.get("properties", {})
        level = classify_alert(props.get("event", ""))
        geocode = props.get("geocode") or {}
        for same in geocode.get("SAME", []) or []:
            fips = same_to_county_fips(same)
            if not fips:
                continue
            old = county_levels.get(fips)
            if old is None or ALERT_PRIORITIES[level] > ALERT_PRIORITIES[old]:
                county_levels[fips] = level
    return county_levels


def iter_rings(geometry: dict):
    geom_type = geometry.get("type")
    coords = geometry.get("coordinates", [])
    if geom_type == "Polygon":
        for ring in coords[:1]:
            yield ring
    elif geom_type == "MultiPolygon":
        for polygon in coords:
            for ring in polygon[:1]:
                yield ring


def geometry_bounds(features: list[dict]) -> tuple[float, float, float, float]:
    xs = []
    ys = []
    for feature in features:
        for ring in iter_rings(feature.get("geometry", {})):
            for lon, lat in ring:
                xs.append(lon)
                ys.append(lat)
    if not xs or not ys:
        raise RuntimeError("County geometry did not contain polygon points")
    return min(xs), min(ys), max(xs), max(ys)


def make_projector(bounds, width: int, height: int, margin: int):
    min_lon, min_lat, max_lon, max_lat = bounds
    span_lon = max(max_lon - min_lon, 0.0001)
    span_lat = max(max_lat - min_lat, 0.0001)
    sx = (width - margin * 2) / span_lon
    sy = (height - margin * 2) / span_lat
    scale = min(sx, sy)
    map_w = span_lon * scale
    map_h = span_lat * scale
    ox = (width - map_w) / 2.0
    oy = (height - map_h) / 2.0

    def project(lon: float, lat: float) -> tuple[int, int]:
        x = ox + (lon - min_lon) * scale
        y = oy + (max_lat - lat) * scale
        return round(x), round(y)

    return project


def load_font(size: int):
    candidates = [
        "C:/Windows/Fonts/segoeui.ttf",
        "C:/Windows/Fonts/arial.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ]
    for path in candidates:
        try:
            return ImageFont.truetype(path, size)
        except Exception:
            pass
    return ImageFont.load_default()


def draw_label(draw: ImageDraw.ImageDraw, xy, text: str, font, fill):
    x, y = xy
    draw.text((x + 1, y + 1), text, font=font, fill=(0, 0, 0))
    draw.text((x, y), text, font=font, fill=fill)


def render_alert_map(
    state_abbr: str,
    counties: list[dict],
    county_levels: dict[str, str],
    width: int,
    height: int,
) -> Image.Image:
    scale = 3
    canvas_w = width * scale
    canvas_h = height * scale
    img = Image.new("RGB", (canvas_w, canvas_h), (12, 15, 20))
    draw = ImageDraw.Draw(img)
    project = make_projector(
        geometry_bounds(counties),
        canvas_w,
        canvas_h,
        margin=10 * scale,
    )

    active_count = 0
    for feature in counties:
        props = feature.get("properties", {})
        geoid = str(props.get("GEOID", ""))
        level = county_levels.get(geoid, "none")
        if level != "none":
            active_count += 1
        fill = ALERT_COLORS[level]

        for ring in iter_rings(feature.get("geometry", {})):
            points = [project(lon, lat) for lon, lat in ring]
            if len(points) >= 3:
                draw.polygon(points, fill=fill)
                draw.line(points + [points[0]], fill=(180, 190, 205), width=scale)

    # A second outline pass makes the outside edge read better on the TFT.
    for feature in counties:
        for ring in iter_rings(feature.get("geometry", {})):
            points = [project(lon, lat) for lon, lat in ring]
            if len(points) >= 3:
                draw.line(points + [points[0]], fill=(235, 240, 248), width=2 * scale)

    title_font = load_font(16 * scale)
    small_font = load_font(10 * scale)
    now = datetime.now().strftime("%m/%d %H:%M")
    draw_label(draw, (6 * scale, 5 * scale), f"{state_abbr} NWS Alerts",
               title_font, (255, 255, 255))
    draw_label(draw, (6 * scale, 25 * scale),
               f"{active_count} counties  {now}", small_font, (205, 214, 225))

    legend = [
        ("warning", "Warn"),
        ("watch", "Watch"),
        ("advisory", "Adv"),
        ("statement", "Stmt"),
        ("other", "Other"),
    ]
    x = 6 * scale
    y = canvas_h - 18 * scale
    for key, label in legend:
        draw.rectangle(
            [x, y + 2 * scale, x + 8 * scale, y + 10 * scale],
            fill=ALERT_COLORS[key],
            outline=(235, 240, 248),
            width=scale,
        )
        draw.text((x + 11 * scale, y), label, font=small_font,
                  fill=(235, 240, 248))
        x += 60 * scale

    resample = getattr(getattr(Image, "Resampling", Image), "LANCZOS")
    return img.resize((width, height), resample)


def image_to_rgb565_rows(img: Image.Image) -> list[bytes]:
    img = img.convert("RGB")
    w, h = img.size
    pixels = img.load()
    rows = []
    for y in range(h):
        row = bytearray(w * 2)
        for x in range(w):
            r, g, b = pixels[x, y]
            # RGB565: red in the high bits, green in the middle, blue low.
            v = ((r & 0xF8) << 8) | ((g & 0xFC) << 3) | (b >> 3)
            row[x * 2] = (v >> 8) & 0xFF
            row[x * 2 + 1] = v & 0xFF
        rows.append(bytes(row))
    return rows


def send_to_display(host: str, port: int, img: Image.Image,
                    timeout: int = 30, connect_retries: int = 4,
                    retry_delay: float = 3.0) -> bool:
    w, h = img.size
    rows = image_to_rgb565_rows(img)
    header = MAGIC + struct.pack(">HHB", w, h, 0)
    total = w * h * 2

    sock = None
    for attempt in range(1, connect_retries + 1):
        print(f"  Connecting {host}:{port} "
              f"(attempt {attempt}/{connect_retries}) ...")
        try:
            sock = socket.create_connection((host, port), timeout=10)
            break
        except OSError as e:
            print(f"  Connect failed: {e}")
            if attempt < connect_retries:
                time.sleep(retry_delay)

    if sock is None:
        return False

    sock.settimeout(timeout)
    try:
        sock.sendall(header)
        sent = 0
        t0 = time.monotonic()
        for y, row in enumerate(rows):
            sock.sendall(row)
            sent += len(row)
            if y % 48 == 0 or y == h - 1:
                pct = sent * 100 // total
                rate = sent / max(time.monotonic() - t0, 0.001) / 1024
                print(f"\r  Sending {pct:3d}%  {rate:.0f} KB/s",
                      end="", flush=True)
        print()

        reply = b""
        while b"\n" not in reply:
            chunk = sock.recv(16)
            if not chunk:
                break
            reply += chunk
        ok = reply.strip().decode("ascii", errors="replace") == "OK"
        print(f"  ESP32: {'OK' if ok else 'ERR'}")
        return ok
    except socket.timeout:
        print("  Socket timed out")
        return False
    except OSError as e:
        print(f"  Socket error: {e}")
        return False
    finally:
        sock.close()


def run_once(args, counties):
    source_w, source_h = source_size_for_rotation(args.rotation)
    print(f"Fetching active NWS alerts for {args.state} ...")
    levels = fetch_alert_levels(args.state)
    print(f"  Counties with active SAME-coded alerts: {len(levels)}")
    img = render_alert_map(args.state, counties, levels, source_w, source_h)
    img = rotate_image_pixels(img, args.rotation)

    if args.preview:
        img.save(args.preview)
        print(f"  Preview saved: {args.preview}")

    return send_to_display(args.host, args.port, img)


def main():
    parser = argparse.ArgumentParser(
        description="NWS state county alert map -> ESP32 TFT"
    )
    parser.add_argument("--state", required=True,
                        help="Two-letter state abbreviation, e.g. NC")
    parser.add_argument("--host", required=True,
                        help="ESP32 IP address")
    parser.add_argument("--port", type=int, default=TCP_PORT,
                        help=f"ESP32 TCP port (default: {TCP_PORT})")
    parser.add_argument("--interval", type=int, default=300,
                        help="Alert refresh interval in seconds (default: 300)")
    parser.add_argument("--rotation", type=int, default=0, choices=[0, 1, 2, 3],
                        help="Image rotation: 0=portrait 1=90 2=180 3=270")
    parser.add_argument("--preview",
                        help="Optional path to save the rendered preview image")
    args = parser.parse_args()
    args.state = args.state.upper()

    if args.state not in STATE_FIPS:
        valid = ", ".join(sorted(STATE_FIPS))
        sys.exit(f"Unsupported state {args.state!r}. Valid: {valid}")
    if args.interval < 30:
        sys.exit("--interval must be at least 30 seconds")

    print(f"Fetching county geometry for {args.state} ...")
    counties = fetch_counties(args.state)
    print(f"  Loaded {len(counties)} counties")

    while True:
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        print(f"\n-- Alert frame {ts} --")
        try:
            ok = run_once(args, counties)
            print(f"  Frame {'sent' if ok else 'failed'}")
        except Exception as e:
            print(f"  Frame error: {e}")

        print(f"  Next in {args.interval}s")
        time.sleep(args.interval)


if __name__ == "__main__":
    main()
