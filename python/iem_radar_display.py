#!/usr/bin/env python3
"""
iem_radar_display.py

Fetches a live NEXRAD radar image centered on a ZIP code, lat/lon pair, or
SAME/NWS county or zone code from the Iowa Environmental Mesonet (IEM) and sends
it to the ESP32 TFT display over TCP.
Repeats at a configurable interval.

Radar source : IEM NEXRAD N0Q CONUS Composite WMS
               https://mesonet.agron.iastate.edu/cgi-bin/wms/nexrad/n0q.cgi
               Free, no API key, no zoom limit, ~5 min updates.
               N0Q = 8-bit base reflectivity (higher resolution than N0R).
Map base     : OpenStreetMap tiles (any zoom)
Display      : raw RGB565 via the RGB! TCP protocol
               Header: MAGIC(4) + W(2BE) + H(2BE) + ROTATION(1) = 9 bytes
               Image pixels are rotated in Python into the fixed 320×480
               frame, then sent with display rotation 0 so the ESP32 draws
               the bitmap as-is instead of only changing address order.

Usage:
    python iem_radar_display.py --zip 27587 --host 192.168.1.42
    python iem_radar_display.py --lat 35.9799 --lon -78.5097 --host 192.168.1.42
    python iem_radar_display.py --county NCC183 --host 192.168.1.42
    python iem_radar_display.py --zip 27587 --host 192.168.1.42 --rotation 1
    python iem_radar_display.py --zip 27587 --host 192.168.1.42 --zoom 9 --webport 8080

Then open http://localhost:8080 (or http://<your-LAN-IP>:8080
from any other device on the same network) to control the display.

Zoom guide (approximate km across the 320-px display width):
    5  ~500 km   6  ~250 km   7  ~125 km   8  ~60 km  (default)
    9   ~30 km  10   ~15 km  11    ~8 km  12   ~4 km

Requirements:
    pip install pillow requests
"""

import argparse
import io
import json
import math
import re
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import parse_qs, urlparse
import socket
import struct
import sys
import time
from datetime import datetime, timezone

try:
    import requests
except ImportError:
    sys.exit("requests is required:  pip install requests")

try:
    from PIL import Image, ImageDraw, ImageFont, ImageEnhance
except ImportError:
    sys.exit("Pillow is required:  pip install pillow")

# ── Display ───────────────────────────────────────────────────────────────────
DISPLAY_W = 320
DISPLAY_H = 480
TCP_PORT  = 5555
API_PORT  = 8765
MAGIC     = b"RGB!"
INFO_BANNER_H = 24

# ── Map sources ───────────────────────────────────────────────────────────────
OSM_HOST  = "https://tile.openstreetmap.org"
TILE_SIZE = 256

# IEM NEXRAD N0Q WMS – free, no key, no zoom limit, EPSG:4326
# N0Q = 8-bit base reflectivity composite (higher res than N0R)
# Layer name: nexrad-n0q-900913  (also accepts EPSG:4326 bbox)
IEM_WMS = "https://mesonet.agron.iastate.edu/cgi-bin/wms/nexrad/n0q.cgi"
IEM_LAYER = "nexrad-n0q-900913"   # the single composite layer this CGI exposes

# Nominatim ZIP → lat/lon
NOMINATIM_URL = "https://nominatim.openstreetmap.org/search"

# NWS active alerts GeoJSON. Alert geometries are drawn on the radar map when
# enabled.
NWS_ALERTS = "https://api.weather.gov/alerts/active"
NWS_ZONES = "https://api.weather.gov/zones"
NWS_ALERT_POLL_SECONDS = 60
NWS_ALERT_FILL_OPACITY = 0.25
NWS_ALERT_COLORS = {
    "statement":       (40, 110, 235),
    "warning":         (225, 38, 38),
    "tornado_warning": (245, 130, 32),
}
NWS_ALERT_PRIORITY = {
    "statement":       1,
    "warning":         2,
    "tornado_warning": 3,
}

STATE_BY_FIPS = {
    "01": "AL", "02": "AK", "04": "AZ", "05": "AR", "06": "CA",
    "08": "CO", "09": "CT", "10": "DE", "11": "DC", "12": "FL",
    "13": "GA", "15": "HI", "16": "ID", "17": "IL", "18": "IN",
    "19": "IA", "20": "KS", "21": "KY", "22": "LA", "23": "ME",
    "24": "MD", "25": "MA", "26": "MI", "27": "MN", "28": "MS",
    "29": "MO", "30": "MT", "31": "NE", "32": "NV", "33": "NH",
    "34": "NJ", "35": "NM", "36": "NY", "37": "NC", "38": "ND",
    "39": "OH", "40": "OK", "41": "OR", "42": "PA", "44": "RI",
    "45": "SC", "46": "SD", "47": "TN", "48": "TX", "49": "UT",
    "50": "VT", "51": "VA", "53": "WA", "54": "WV", "55": "WI",
    "56": "WY", "60": "AS", "66": "GU", "69": "MP", "72": "PR",
    "78": "VI",
}

# ── Shared HTTP session ───────────────────────────────────────────────────────
_session = requests.Session()
_session.headers.update({
    "User-Agent": "ESP32-IEMRadar/1.0",
    "Accept": "application/geo+json, application/json, image/png, */*",
})

# ─────────────────────────────────────────────────────────────────────────────
# Geo helpers
# ─────────────────────────────────────────────────────────────────────────────

def zip_to_latlon(zipcode: str) -> tuple[float, float]:
    """Return (lat, lon) for a US ZIP code via Nominatim (no key required)."""
    r = _session.get(NOMINATIM_URL, params={
        "postalcode": zipcode, "country": "US",
        "format": "json", "limit": 1,
    }, timeout=10)
    r.raise_for_status()
    data = r.json()
    if not data:
        raise ValueError(f"ZIP {zipcode!r} not found")
    return float(data[0]["lat"]), float(data[0]["lon"])


def nws_code_to_zone(code: str) -> tuple[str, str]:
    """Return (zone_type, zone_id) from a 6-digit SAME or NWS zone code."""
    normalized = code.strip().upper()
    if re.fullmatch(r"\d{6}", normalized):
        state = STATE_BY_FIPS.get(normalized[1:3])
        if not state:
            raise ValueError(f"unknown SAME state FIPS {normalized[1:3]!r}")
        return "county", f"{state}C{normalized[3:]}"
    if re.fullmatch(r"[A-Z]{2}C\d{3}", normalized):
        return "county", normalized
    if re.fullmatch(r"[A-Z]{2}Z\d{3}", normalized):
        return "forecast", normalized
    raise ValueError(
        "use a 6-digit SAME code like 037183, an NWS county code like NCC183, "
        "or a forecast zone like NCZ183"
    )


def exterior_rings(geometry: dict) -> list[list[list[float]]]:
    gtype = geometry.get("type")
    coordinates = geometry.get("coordinates")
    if gtype == "Polygon" and isinstance(coordinates, list) and coordinates:
        return [coordinates[0]]
    if gtype == "MultiPolygon" and isinstance(coordinates, list):
        return [polygon[0] for polygon in coordinates if polygon]
    raise RuntimeError(f"unsupported NWS zone geometry type {gtype!r}")


def polygon_centroid(ring: list[list[float]]) -> tuple[float, float, float]:
    if ring[0] != ring[-1]:
        ring = [*ring, ring[0]]

    area = 0.0
    cx = 0.0
    cy = 0.0
    for (x1, y1), (x2, y2) in zip(ring, ring[1:]):
        cross = x1 * y2 - x2 * y1
        area += cross
        cx += (x1 + x2) * cross
        cy += (y1 + y2) * cross

    area *= 0.5
    if abs(area) < 1e-12:
        raise RuntimeError("NWS zone geometry has zero polygon area")
    return cx / (6.0 * area), cy / (6.0 * area), abs(area)


def geometry_center(geometry: dict) -> tuple[float, float]:
    total_area = 0.0
    weighted_lon = 0.0
    weighted_lat = 0.0
    for ring in exterior_rings(geometry):
        lon, lat, area = polygon_centroid(ring)
        weighted_lon += lon * area
        weighted_lat += lat * area
        total_area += area
    if total_area <= 0.0:
        raise RuntimeError("NWS zone geometry did not contain polygon area")
    return weighted_lat / total_area, weighted_lon / total_area


def nws_code_to_latlon(code: str) -> tuple[float, float, str]:
    """Return (lat, lon, normalized zone id) for a SAME/NWS county or zone code."""
    zone_type, zone_id = nws_code_to_zone(code)
    r = _session.get(f"{NWS_ZONES}/{zone_type}/{zone_id}", timeout=10)
    r.raise_for_status()
    payload = r.json()
    geometry = payload.get("geometry")
    if not geometry:
        raise RuntimeError(f"NWS API returned no geometry for {zone_id}")
    lat, lon = geometry_center(geometry)
    validate_latlon(lat, lon)
    return lat, lon, zone_id


def validate_latlon(lat: float, lon: float) -> None:
    if not (-85.0 <= lat <= 85.0):
        raise ValueError("lat must be between -85 and 85")
    if not (-180.0 <= lon <= 180.0):
        raise ValueError("lon must be between -180 and 180")


def deg2tile(lat: float, lon: float, z: int) -> tuple[int, int]:
    """Lat/lon → OSM tile (x, y) at zoom z."""
    n = 2 ** z
    x = int((lon + 180.0) / 360.0 * n)
    y = int((1.0 - math.asinh(math.tan(math.radians(lat))) / math.pi) / 2.0 * n)
    return x, y


def latlon_to_canvas_px(lat: float, lon: float,
                         z: int, tx0: int, ty0: int) -> tuple[float, float]:
    """Pixel coords of (lat,lon) on a canvas whose top-left tile is (tx0,ty0)."""
    n = 2 ** z
    px = (lon + 180.0) / 360.0 * n * TILE_SIZE - tx0 * TILE_SIZE
    py = (1.0 - math.asinh(math.tan(math.radians(lat))) / math.pi) \
         / 2.0 * n * TILE_SIZE - ty0 * TILE_SIZE
    return px, py


def crop_bbox_latlon(z: int, tx0: int, ty0: int,
                     crop_left: int, crop_top: int,
                     crop_w: int = DISPLAY_W,
                     crop_h: int = DISPLAY_H) -> tuple[float, float, float, float]:
    """
    Return (min_lat, min_lon, max_lat, max_lon) for the requested
    crop window in WGS-84 degrees.  Used to build the WMS BBOX.
    """
    n = 2 ** z

    def px_to_lon(px: float) -> float:
        return (px / (n * TILE_SIZE) + tx0 / n) * 360.0 - 180.0

    def px_to_lat(py: float) -> float:
        merc = math.pi * (1 - 2 * (py / (n * TILE_SIZE) + ty0 / n))
        return math.degrees(math.atan(math.sinh(merc)))

    min_lon = px_to_lon(crop_left)
    max_lon = px_to_lon(crop_left + crop_w)
    max_lat = px_to_lat(crop_top)           # y increases downward
    min_lat = px_to_lat(crop_top + crop_h)
    return min_lat, min_lon, max_lat, max_lon


def map_view_for_center(lat: float, lon: float, zoom: int,
                        width: int, height: int) -> dict:
    """Return tile/crop metadata for the display crop centered on lat/lon."""
    cx_tile, cy_tile = deg2tile(lat, lon, zoom)
    tiles_x = math.ceil(width / TILE_SIZE) + 2
    tiles_y = math.ceil(height / TILE_SIZE) + 2
    tx0 = cx_tile - tiles_x // 2
    ty0 = cy_tile - tiles_y // 2
    canvas_w = tiles_x * TILE_SIZE
    canvas_h = tiles_y * TILE_SIZE

    px, py = latlon_to_canvas_px(lat, lon, zoom, tx0, ty0)
    crop_left = int(px) - width // 2
    crop_top = int(py) - height // 2
    crop_left = max(0, min(crop_left, canvas_w - width))
    crop_top = max(0, min(crop_top, canvas_h - height))

    min_lat, min_lon, max_lat, max_lon = crop_bbox_latlon(
        zoom, tx0, ty0, crop_left, crop_top, width, height)

    return {
        "tiles_x": tiles_x,
        "tiles_y": tiles_y,
        "tx0": tx0,
        "ty0": ty0,
        "crop_left": crop_left,
        "crop_top": crop_top,
        "bbox": (min_lat, min_lon, max_lat, max_lon),
    }


# ─────────────────────────────────────────────────────────────────────────────
# OSM base map
# ─────────────────────────────────────────────────────────────────────────────

def fetch_osm_tile(z: int, x: int, y: int) -> Image.Image:
    url = f"{OSM_HOST}/{z}/{x}/{y}.png"
    r = _session.get(url, timeout=10)
    r.raise_for_status()
    return Image.open(io.BytesIO(r.content)).convert("RGBA")


def build_osm_canvas(z: int, tx0: int, ty0: int,
                     tiles_x: int, tiles_y: int) -> Image.Image:
    """Stitch OSM tiles into a single RGBA canvas."""
    canvas = Image.new("RGBA", (tiles_x * TILE_SIZE, tiles_y * TILE_SIZE),
                       (50, 50, 50, 255))
    for dy in range(tiles_y):
        for dx in range(tiles_x):
            tx, ty = tx0 + dx, ty0 + dy
            try:
                tile = fetch_osm_tile(z, tx, ty)
                canvas.paste(tile, (dx * TILE_SIZE, dy * TILE_SIZE))
                print(f"    OSM {z}/{tx}/{ty} ✓", end="\r", flush=True)
            except Exception as e:
                print(f"    OSM {z}/{tx}/{ty} ✗ {e}")
    print()
    return canvas


# ─────────────────────────────────────────────────────────────────────────────
# IEM NEXRAD N0Q WMS radar fetcher
# ─────────────────────────────────────────────────────────────────────────────

def fetch_iem_radar(min_lat: float, min_lon: float,
                    max_lat: float, max_lon: float,
                    width: int, height: int) -> Image.Image:
    """
    Fetch a radar overlay from the IEM NEXRAD N0Q WMS service.

    Uses WMS 1.1.1 with SRS=EPSG:4326 and BBOX in (minLon, minLat, maxLon, maxLat)
    axis order (lon/lat for 1.1.1).  Returns a transparent RGBA image.

    The IEM WMS has no zoom cap — any bounding box and output size works.
    """
    bbox = f"{min_lon},{min_lat},{max_lon},{max_lat}"
    params = {
        "SERVICE":     "WMS",
        "VERSION":     "1.1.1",
        "REQUEST":     "GetMap",
        "LAYERS":      IEM_LAYER,
        "STYLES":      "",
        "SRS":         "EPSG:4326",
        "BBOX":        bbox,
        "WIDTH":       str(width),
        "HEIGHT":      str(height),
        "FORMAT":      "image/png",
        "TRANSPARENT": "TRUE",
    }
    r = _session.get(IEM_WMS, params=params, timeout=20)
    r.raise_for_status()

    # Verify we got an image back, not a WMS error XML
    ct = r.headers.get("Content-Type", "")
    if "image" not in ct:
        raise RuntimeError(f"IEM WMS returned non-image: {ct}\n{r.text[:300]}")

    return Image.open(io.BytesIO(r.content)).convert("RGBA")


# ─────────────────────────────────────────────────────────────────────────────
# NWS alert polygons
# ─────────────────────────────────────────────────────────────────────────────

def classify_nws_alert(event: str) -> str | None:
    event = event.lower()
    if "tornado warning" in event:
        return "tornado_warning"
    if "warning" in event:
        return "warning"
    if "statement" in event:
        return "statement"
    return None


def iter_geojson_rings(geometry: dict):
    geom_type = geometry.get("type")
    coords = geometry.get("coordinates", [])
    if geom_type == "Polygon":
        if coords:
            yield coords[0]
    elif geom_type == "MultiPolygon":
        for polygon in coords:
            if polygon:
                yield polygon[0]


def ring_intersects_bbox(ring, min_lat: float, min_lon: float,
                         max_lat: float, max_lon: float) -> bool:
    if not ring:
        return False
    lons = [pt[0] for pt in ring if len(pt) >= 2]
    lats = [pt[1] for pt in ring if len(pt) >= 2]
    if not lons or not lats:
        return False
    return not (
        max(lons) < min_lon or min(lons) > max_lon or
        max(lats) < min_lat or min(lats) > max_lat
    )


def _ccw(a: tuple[int, int], b: tuple[int, int],
         c: tuple[int, int]) -> bool:
    return (c[1] - a[1]) * (b[0] - a[0]) > (b[1] - a[1]) * (c[0] - a[0])


def _segments_intersect(a: tuple[int, int], b: tuple[int, int],
                        c: tuple[int, int], d: tuple[int, int]) -> bool:
    return _ccw(a, c, d) != _ccw(b, c, d) and _ccw(a, b, c) != _ccw(a, b, d)


def _point_in_polygon(point: tuple[int, int],
                      polygon: list[tuple[int, int]]) -> bool:
    x, y = point
    inside = False
    j = len(polygon) - 1
    for i in range(len(polygon)):
        xi, yi = polygon[i]
        xj, yj = polygon[j]
        if ((yi > y) != (yj > y) and
                x < (xj - xi) * (y - yi) / ((yj - yi) or 1e-9) + xi):
            inside = not inside
        j = i
    return inside


def projected_ring_visible(points: list[tuple[int, int]],
                           width: int, height: int) -> bool:
    if len(points) < 2:
        return False

    min_x = min(x for x, _y in points)
    max_x = max(x for x, _y in points)
    min_y = min(y for _x, y in points)
    max_y = max(y for _x, y in points)
    if max_x < 0 or min_x >= width or max_y < 0 or min_y >= height:
        return False

    if any(0 <= x < width and 0 <= y < height for x, y in points):
        return True

    rect_edges = [
        ((0, 0), (width - 1, 0)),
        ((width - 1, 0), (width - 1, height - 1)),
        ((width - 1, height - 1), (0, height - 1)),
        ((0, height - 1), (0, 0)),
    ]
    closed = points + [points[0]]
    for a, b in zip(closed, closed[1:]):
        for c, d in rect_edges:
            if _segments_intersect(a, b, c, d):
                return True

    return len(points) >= 3 and _point_in_polygon((width // 2, height // 2),
                                                  points)


def normalize_projected_ring(points: list[tuple[int, int]]
                             ) -> tuple[tuple[int, int], ...]:
    cleaned = []
    for point in points:
        if not cleaned or cleaned[-1] != point:
            cleaned.append(point)
    if len(cleaned) > 1 and cleaned[0] == cleaned[-1]:
        cleaned.pop()
    if not cleaned:
        return tuple()

    def rotations(seq):
        for idx in range(len(seq)):
            yield tuple(seq[idx:] + seq[:idx])

    forward = min(rotations(cleaned))
    reverse = min(rotations(list(reversed(cleaned))))
    return min(forward, reverse)


def count_mask_regions(mask: Image.Image, min_pixels: int = 1) -> int:
    """Count connected visible regions in a 1-bit-ish rendered alert mask."""
    mask = mask.convert("L")
    width, height = mask.size
    pixels = mask.load()
    seen = bytearray(width * height)
    regions = 0

    for start_y in range(height):
        row_offset = start_y * width
        for start_x in range(width):
            idx = row_offset + start_x
            if seen[idx] or pixels[start_x, start_y] == 0:
                continue

            regions += 1
            seen[idx] = 1
            stack = [(start_x, start_y)]
            region_pixels = 0

            while stack:
                x, y = stack.pop()
                region_pixels += 1
                for ny in range(max(0, y - 1), min(height, y + 2)):
                    nrow = ny * width
                    for nx in range(max(0, x - 1), min(width, x + 2)):
                        nidx = nrow + nx
                        if not seen[nidx] and pixels[nx, ny] != 0:
                            seen[nidx] = 1
                            stack.append((nx, ny))

            if region_pixels < min_pixels:
                regions -= 1

    return regions


def fetch_nws_alert_polygons(min_lat: float, min_lon: float,
                             max_lat: float, max_lon: float) -> list[dict]:
    r = _session.get(NWS_ALERTS, timeout=30)
    r.raise_for_status()
    data = r.json()

    alerts = []
    for feature in data.get("features", []):
        props = feature.get("properties", {})
        level = classify_nws_alert(props.get("event", ""))
        if level is None:
            continue
        geometry = feature.get("geometry") or {}
        rings = [
            ring for ring in iter_geojson_rings(geometry)
            if ring_intersects_bbox(ring, min_lat, min_lon, max_lat, max_lon)
        ]
        if rings:
            alerts.append({
                "id": feature.get("id") or props.get("id", ""),
                "event": props.get("event", ""),
                "level": level,
                "updated": props.get("updated", ""),
                "effective": props.get("effective", ""),
                "expires": props.get("expires", ""),
                "ends": props.get("ends", ""),
                "status": props.get("status", ""),
                "messageType": props.get("messageType", ""),
                "severity": props.get("severity", ""),
                "certainty": props.get("certainty", ""),
                "urgency": props.get("urgency", ""),
                "rings": rings,
            })

    alerts.sort(key=lambda item: NWS_ALERT_PRIORITY[item["level"]])
    return alerts


def nws_alert_signature(alerts: list[dict]) -> str:
    """Stable signature for visible NWS alert identity, timing, and geometry."""
    items = []
    for alert in alerts:
        rings = []
        for ring in alert["rings"]:
            rings.append([
                [round(float(lon), 4), round(float(lat), 4)]
                for lon, lat, *_ in ring
            ])
        items.append({
            "id": alert.get("id", ""),
            "event": alert.get("event", ""),
            "level": alert.get("level", ""),
            "updated": alert.get("updated", ""),
            "effective": alert.get("effective", ""),
            "expires": alert.get("expires", ""),
            "ends": alert.get("ends", ""),
            "status": alert.get("status", ""),
            "messageType": alert.get("messageType", ""),
            "severity": alert.get("severity", ""),
            "certainty": alert.get("certainty", ""),
            "urgency": alert.get("urgency", ""),
            "rings": rings,
        })
    items.sort(key=lambda item: (
        item["level"], item["id"], item["event"], item["updated"],
        json.dumps(item["rings"], separators=(",", ":")),
    ))
    return json.dumps(items, sort_keys=True, separators=(",", ":"))


def draw_nws_alert_polygons(img: Image.Image, draw: ImageDraw.ImageDraw,
                            alerts: list[dict],
                            zoom: int, tx0: int, ty0: int,
                            crop_left: int, crop_top: int,
                            width: int, height: int,
                            fill_opacity: float = NWS_ALERT_FILL_OPACITY) -> int:
    drawn = 0
    line_w = 2 if min(width, height) <= 320 else 3
    fill_opacity = max(0.0, min(1.0, fill_opacity))
    fill_alpha = round(fill_opacity * 255)
    projected_rings = {}

    for alert in alerts:
        color = NWS_ALERT_COLORS[alert["level"]]
        for ring in alert["rings"]:
            points = []
            for lon, lat, *_ in ring:
                x, y = latlon_to_canvas_px(lat, lon, zoom, tx0, ty0)
                points.append((round(x - crop_left), round(y - crop_top)))
            if not projected_ring_visible(points, width, height):
                continue
            key = normalize_projected_ring(points)
            if len(key) >= 2:
                projected_rings[key] = (color, list(key))

    count_layer = Image.new("L", (width, height), 0)
    count_draw = ImageDraw.Draw(count_layer)
    for _color, points in projected_rings.values():
        if fill_alpha > 0 and len(points) >= 3:
            count_draw.polygon(points, fill=255)
        elif fill_alpha == 0:
            count_draw.line(points + [points[0]], fill=255, width=line_w)

    count_height = max(1, height - INFO_BANNER_H)
    count_mask = count_layer.crop((0, 0, width, count_height))
    min_region_pixels = max(25, (width * count_height) // 2000)
    drawn = count_mask_regions(count_mask, min_region_pixels)

    if fill_alpha > 0:
        fill_layer = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        fill_draw = ImageDraw.Draw(fill_layer)
        for color, points in projected_rings.values():
            if len(points) >= 3:
                fill_draw.polygon(points, fill=(*color, fill_alpha))
        filled = Image.alpha_composite(img.convert("RGBA"), fill_layer)
        img.paste(filled.convert("RGB"))
        draw = ImageDraw.Draw(img)

    for color, points in projected_rings.values():
        draw.line(points + [points[0]], fill=color, width=line_w)

    return drawn


# ─────────────────────────────────────────────────────────────────────────────
# Image composition
# ─────────────────────────────────────────────────────────────────────────────

def build_radar_image(lat: float, lon: float, zoom: int,
                      brightness: float = 1.0,
                      radar_opacity: float = 1.0,
                      alert_polygons: bool = False,
                      alert_fill_opacity: float = NWS_ALERT_FILL_OPACITY,
                      width: int = DISPLAY_W,
                      height: int = DISPLAY_H) -> Image.Image:
    """
    Build a width × height composite:
      1. OSM base map (tiled, any zoom)
      2. IEM NEXRAD N0Q radar overlay (WMS bounding-box, any zoom, no cap)
      3. Optional NWS warning/statement polygon fills/outlines
      4. Yellow crosshair at ZIP centre
      5. Timestamp + source banner
    """
    # ── Tile grid ─────────────────────────────────────────────────────────
    view = map_view_for_center(lat, lon, zoom, width, height)
    tiles_x = view["tiles_x"]
    tiles_y = view["tiles_y"]
    tx0 = view["tx0"]
    ty0 = view["ty0"]

    print(f"  OSM grid {tiles_x}×{tiles_y} tiles at zoom {zoom}")

    # ── 1. OSM base ───────────────────────────────────────────────────────
    base = build_osm_canvas(zoom, tx0, ty0, tiles_x, tiles_y)

    # ── Crop window centred on ZIP ────────────────────────────────────────
    crop_left = view["crop_left"]
    crop_top = view["crop_top"]

    # ── 2. IEM radar overlay ──────────────────────────────────────────────
    min_lat, min_lon, max_lat, max_lon = view["bbox"]

    print(f"  BBOX: {min_lat:.4f},{min_lon:.4f} → {max_lat:.4f},{max_lon:.4f}")
    print(f"  Fetching IEM NEXRAD N0Q …", end=" ", flush=True)

    radar_ok = False
    try:
        radar = fetch_iem_radar(min_lat, min_lon, max_lat, max_lon,
                                width, height)
        img = base.crop((crop_left, crop_top,
                         crop_left + width, crop_top + height))
        # Apply base map brightness
        if brightness != 1.0:
            img = ImageEnhance.Brightness(img.convert("RGB")).enhance(brightness)
            img = img.convert("RGBA")
        # Apply radar overlay opacity
        if radar_opacity != 1.0:
            r2, g2, b2, a2 = radar.split()
            a2 = a2.point(lambda p: int(p * max(0.0, min(1.0, radar_opacity))))
            radar = Image.merge("RGBA", (r2, g2, b2, a2))
        img.alpha_composite(radar)
        img = img.convert("RGB")
        radar_ok = True
        print("✓")
    except Exception as e:
        print(f"✗  {e}")
        # Fall back to base map only so the display still updates
        img = base.crop((crop_left, crop_top,
                         crop_left + width, crop_top + height)
                        ).convert("RGB")
        if brightness != 1.0:
            img = ImageEnhance.Brightness(img).enhance(brightness)

    # ── 3. NWS alert polygon fills/outlines ───────────────────────────────
    draw = ImageDraw.Draw(img)
    alert_count = 0
    if alert_polygons:
        print("  Fetching NWS alert polygons ...", end=" ", flush=True)
        try:
            alerts = fetch_nws_alert_polygons(min_lat, min_lon, max_lat, max_lon)
            alert_count = draw_nws_alert_polygons(
                img, draw, alerts, zoom, tx0, ty0, crop_left, crop_top,
                width, height, alert_fill_opacity)
            print(f"{alert_count} polygon(s)")
        except Exception as e:
            print(f"failed: {e}")

    # ── 4. Crosshair ──────────────────────────────────────────────────────
    draw = ImageDraw.Draw(img)
    cx, cy = width // 2, height // 2
    arm = 12
    draw.line([(cx - arm, cy), (cx + arm, cy)], fill=(255, 255, 0), width=2)
    draw.line([(cx, cy - arm), (cx, cy + arm)], fill=(255, 255, 0), width=2)
    draw.ellipse([cx - arm, cy - arm, cx + arm, cy + arm],
                 outline=(255, 255, 0), width=1)

    # ── 5. Info banner ─────────────────────────────────────────────────────
    banner_h = INFO_BANNER_H
    banner = Image.new("RGBA", (width, banner_h), (0, 0, 0, 190))
    img_rgba = img.convert("RGBA")
    img_rgba.alpha_composite(banner, dest=(0, height - banner_h))
    img = img_rgba.convert("RGB")

    draw = ImageDraw.Draw(img)
    try:
        font = ImageFont.truetype(
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 13)
    except Exception:
        font = ImageFont.load_default()

    local_time = datetime.now().strftime("%m/%d %H:%M")
    status = "IEM N0Q" if radar_ok else "IEM N0Q (FAIL)"
    alerts_label = f"  NWS {alert_count}" if alert_polygons else ""
    label = f"{status}  z{zoom}{alerts_label}  {local_time}"
    draw.text((4, height - banner_h + 5), label,
              fill=(255, 255, 255), font=font)

    return img


# ─────────────────────────────────────────────────────────────────────────────
# RGB565 conversion
# ─────────────────────────────────────────────────────────────────────────────

def image_to_rgb565_rows(img: Image.Image) -> list[bytes]:
    img = img.convert("RGB")
    w, h = img.size
    pixels = img.load()
    rows = []
    for y in range(h):
        row = bytearray(w * 2)
        for x in range(w):
            r, g, b = pixels[x, y]
            # RGB565: red in high bits, blue in low bits
            v = ((r & 0xF8) << 8) | ((g & 0xFC) << 3) | (b >> 3)
            row[x * 2]     = (v >> 8) & 0xFF
            row[x * 2 + 1] =  v       & 0xFF
        rows.append(bytes(row))
    return rows


def rotate_image_pixels(img: Image.Image, rotation: int) -> Image.Image:
    """Rotate the bitmap itself inside the physical 320x480 display frame."""
    rotation = rotation % 4
    if rotation == 0:
        return img.convert("RGB")

    if rotation == 1:
        rotated = img.transpose(Image.Transpose.ROTATE_270)  # 90 degrees CW
    elif rotation == 2:
        rotated = img.transpose(Image.Transpose.ROTATE_180)
    elif rotation == 3:
        rotated = img.transpose(Image.Transpose.ROTATE_90)   # 270 degrees CW
    else:
        raise ValueError(f"invalid rotation {rotation}")

    return rotated.convert("RGB")


def source_size_for_rotation(rotation: int) -> tuple[int, int]:
    """Return the image size to compose before rotating into 320x480."""
    if rotation % 2:
        return DISPLAY_H, DISPLAY_W
    return DISPLAY_W, DISPLAY_H


# ─────────────────────────────────────────────────────────────────────────────
# TCP send
# ─────────────────────────────────────────────────────────────────────────────

def send_to_display(host: str, port: int, img: Image.Image,
                    rotation: int = 0, timeout: int = 30,
                    connect_retries: int = 4,
                    retry_delay: float = 3.0) -> bool:
    w, h   = img.size
    rows   = image_to_rgb565_rows(img)
    header = MAGIC + struct.pack(">HHB", w, h, rotation)
    total  = w * h * 2

    sock = None
    for attempt in range(1, connect_retries + 1):
        print(f"  Connecting {host}:{port} "
              f"(attempt {attempt}/{connect_retries}) …")
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
        t0   = time.monotonic()
        sent = 0
        for y, row in enumerate(rows):
            sock.sendall(row)
            sent += len(row)
            if y % 48 == 0 or y == h - 1:
                pct  = sent * 100 // total
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
        print(f"  ESP32: {'OK ✓' if ok else 'ERR ✗'}")
        return ok
    except socket.timeout:
        print("  Socket timed out")
        return False
    except OSError as e:
        print(f"  Socket error: {e}")
        return False
    finally:
        sock.close()


def encode_rgb_image_page(img: Image.Image, rotation: int = 0) -> bytes:
    """Return the RGB! image frame understood by the direct TCP and channel firmware."""
    w, h = img.size
    rows = image_to_rgb565_rows(img)
    return MAGIC + struct.pack(">HHB", w, h, rotation) + b"".join(rows)


def read_channel_greeting(sock: socket.socket) -> None:
    old_timeout = sock.gettimeout()
    try:
        sock.settimeout(0.2)
        try:
            data = sock.recv(4096)
        except socket.timeout:
            return
        if data:
            text = data.decode("utf-8", errors="replace").strip()
            if text:
                print(f"  Channel server: {text}")
    finally:
        sock.settimeout(old_timeout)


def publish_to_channel_server(host: str, port: int, channel: str, payload: bytes,
                              timeout: int = 30) -> bool:
    try:
        with socket.create_connection((host, port), timeout=10) as sock:
            sock.settimeout(timeout)
            sock.sendall(f"PUB {channel}\n".encode("utf-8"))
            read_channel_greeting(sock)
            sock.sendall(payload)
        return True
    except OSError as e:
        print(f"  Channel publish failed: {e}")
        return False


def publish_control_channels(host: str, port: int, control_channel: str,
                             channels: list[str]) -> bool:
    payload = json.dumps(channels, separators=(",", ":")).encode("utf-8")
    return publish_to_channel_server(host, port, control_channel, payload)


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────


# ─────────────────────────────────────────────────────────────────────────────
# Shared state  (all access protected by a Lock)
# ─────────────────────────────────────────────────────────────────────────────

class RadarState:
    def __init__(self, zipcode, zoom, rotation, interval, lat, lon,
                 county_code="",
                 brightness=1.0, radar_opacity=1.0, alert_polygons=False,
                 alert_fill_opacity=NWS_ALERT_FILL_OPACITY):
        self._lock        = threading.Lock()
        self.zipcode      = zipcode
        self.county_code  = county_code
        self.center_mode  = "county" if county_code else ("zip" if zipcode else "latlon")
        self.zoom         = zoom
        self.rotation     = rotation   # 0=portrait 1=landscape 2=180 3=270
        self.interval     = interval
        self.lat          = lat
        self.lon          = lon
        self.brightness   = brightness    # 0.5–2.0, 1.0 = no change
        self.radar_opacity = radar_opacity # 0.0–1.0, 1.0 = fully opaque
        self.alert_polygons = alert_polygons
        self.alert_fill_opacity = alert_fill_opacity
        self.status       = "Starting..."
        self.last_sent    = None
        self.frame        = 0

    def get(self):
        with self._lock:
            return (self.zipcode, self.county_code, self.center_mode,
                    self.zoom, self.rotation,
                    self.interval, self.lat, self.lon,
                    self.brightness, self.radar_opacity,
                    self.alert_polygons, self.alert_fill_opacity)

    def update(self, zipcode=None, zoom=None, rotation=None, interval=None,
               lat=None, lon=None, county_code=None,
               brightness=None, radar_opacity=None,
               alert_polygons=None, alert_fill_opacity=None):
        """Update one or more fields.  Re-resolves ZIP if it changed.
        Returns an error string on failure, or None on success."""
        with self._lock:
            if zipcode:
                try:
                    lat, lon = zip_to_latlon(zipcode)
                except Exception as e:
                    return str(e)
                self.zipcode = zipcode
                self.county_code = ""
                self.center_mode = "zip"
                self.lat     = lat
                self.lon     = lon
            elif county_code:
                try:
                    lat, lon, zone_id = nws_code_to_latlon(county_code)
                except Exception as e:
                    return str(e)
                self.zipcode = ""
                self.county_code = zone_id
                self.center_mode = "county"
                self.lat = lat
                self.lon = lon
            elif lat is not None or lon is not None:
                if lat is None or lon is None:
                    return "lat and lon must be provided together"
                try:
                    validate_latlon(lat, lon)
                except Exception as e:
                    return str(e)
                self.zipcode = ""
                self.county_code = ""
                self.center_mode = "latlon"
                self.lat = lat
                self.lon = lon
            if zoom          is not None: self.zoom          = zoom
            if rotation      is not None: self.rotation      = rotation
            if interval      is not None: self.interval      = interval
            if brightness    is not None: self.brightness    = brightness
            if radar_opacity is not None: self.radar_opacity = radar_opacity
            if alert_polygons is not None: self.alert_polygons = alert_polygons
            if alert_fill_opacity is not None:
                self.alert_fill_opacity = alert_fill_opacity
        return None

    def set_status(self, msg):
        with self._lock:
            self.status = msg

    def info(self):
        with self._lock:
            return {
                "zipcode":      self.zipcode,
                "county_code":  self.county_code,
                "center_mode":  self.center_mode,
                "zoom":         self.zoom,
                "rotation":     self.rotation,
                "interval":     self.interval,
                "brightness":   round(self.brightness, 2),
                "radar_opacity": round(self.radar_opacity, 2),
                "alert_polygons": self.alert_polygons,
                "alert_fill_opacity": round(self.alert_fill_opacity, 2),
                "lat":          round(self.lat, 4),
                "lon":          round(self.lon, 4),
                "status":       self.status,
                "last_sent":    (self.last_sent.strftime("%Y-%m-%d %H:%M:%S")
                                 if self.last_sent else "—"),
                "frame":        self.frame,
            }


# ─────────────────────────────────────────────────────────────────────────────
# Radar worker thread
# ─────────────────────────────────────────────────────────────────────────────

def radar_worker(state: RadarState, esp_host: str | None, esp_port: int,
                 trigger: threading.Event, channel_host: str | None = None,
                 channel_port: int = 9000, channel_name: str = "radar"):
    """Runs forever.  Wakes on trigger (immediate update) or interval timeout."""
    while True:
        (zipcode, county_code, center_mode, zoom, rotation, interval,
         lat, lon, brightness, radar_opacity, alert_polygons,
         alert_fill_opacity) = state.get()

        state.set_status("Fetching radar...")
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        print(f"\n-- Frame {state.frame + 1}  {ts} --")
        if center_mode == "zip":
            center_label = zipcode
        elif center_mode == "county":
            center_label = county_code
        else:
            center_label = f"{lat:.4f},{lon:.4f}"
        print(f"   Center={center_label}  zoom={zoom}  rotation={rotation}  "
              f"bright={brightness:.2f}  opacity={radar_opacity:.2f}  "
              f"alerts={'on' if alert_polygons else 'off'}  "
              f"alert_fill={alert_fill_opacity:.2f}")

        try:
            source_w, source_h = source_size_for_rotation(rotation)
            img = build_radar_image(lat, lon, zoom,
                                    brightness=brightness,
                                    radar_opacity=radar_opacity,
                                    alert_polygons=alert_polygons,
                                    alert_fill_opacity=alert_fill_opacity,
                                    width=source_w,
                                    height=source_h)
            img = rotate_image_pixels(img, rotation)
        except Exception as e:
            print(f"   Build failed: {e}")
            state.set_status(f"Error: {e}")
            trigger.wait(timeout=interval)
            trigger.clear()
            continue

        if channel_host:
            state.set_status("Publishing image channel...")
            payload = encode_rgb_image_page(img, rotation=0)
            ok = publish_to_channel_server(channel_host, channel_port,
                                           channel_name, payload)
        else:
            state.set_status("Sending to display...")
            ok = send_to_display(esp_host, esp_port, img, rotation=0)

        with state._lock:
            state.frame    += 1
            state.last_sent = datetime.now()
            state.status    = "OK" if ok else "Send failed"

        print(f"   Next in {interval}s (or on web change)")
        trigger.wait(timeout=interval)
        trigger.clear()


def nws_alert_worker(state: RadarState, trigger: threading.Event,
                     poll_seconds: int = NWS_ALERT_POLL_SECONDS):
    """
    Poll visible NWS alerts while overlays are enabled.

    The first successful poll establishes a baseline.  Later changes wake the
    radar worker so the TFT redraws without waiting for the normal radar
    interval.
    """
    last_signature = None
    while True:
        try:
            (_zipcode, _county_code, _center_mode, zoom, rotation, _interval,
             lat, lon, _brightness, _radar_opacity, alert_polygons,
             _alert_fill_opacity) = state.get()

            if not alert_polygons:
                last_signature = None
                time.sleep(poll_seconds)
                continue

            source_w, source_h = source_size_for_rotation(rotation)
            view = map_view_for_center(lat, lon, zoom, source_w, source_h)
            min_lat, min_lon, max_lat, max_lon = view["bbox"]
            alerts = fetch_nws_alert_polygons(min_lat, min_lon, max_lat, max_lon)
            signature = nws_alert_signature(alerts)

            if last_signature is None:
                last_signature = signature
                print(f"   NWS alert watcher baseline: {len(alerts)} visible")
            elif signature != last_signature:
                last_signature = signature
                print(f"   NWS visible alert change detected: "
                      f"{len(alerts)} visible; updating display")
                trigger.set()
        except Exception as e:
            print(f"   NWS alert watcher failed: {e}")

        time.sleep(poll_seconds)


# ─────────────────────────────────────────────────────────────────────────────
# Web UI  (served by a background thread on --webport)
# ─────────────────────────────────────────────────────────────────────────────

_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>ESP32 Radar Control</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:system-ui,sans-serif;background:#0f172a;color:#e2e8f0;
     min-height:100vh;display:flex;align-items:center;justify-content:center;
     padding:16px}
.card{background:#1e293b;border-radius:16px;padding:28px 32px;width:100%;
      max-width:500px;box-shadow:0 8px 32px rgba(0,0,0,.4)}
h1{font-size:1.4rem;font-weight:700;color:#38bdf8;margin-bottom:4px}
.sub{font-size:.8rem;color:#94a3b8;margin-bottom:24px}
label{display:block;font-size:.75rem;font-weight:600;color:#94a3b8;
      margin-bottom:5px;text-transform:uppercase;letter-spacing:.05em}
.hint{font-size:.78rem;color:#94a3b8;margin:-12px 0 18px;line-height:1.4}
input[type=text],input[type=number],select{
      width:100%;padding:10px 14px;border-radius:8px;
      border:1px solid #334155;background:#0f172a;color:#e2e8f0;
      font-size:1rem;margin-bottom:18px}
input:focus,select:focus{outline:2px solid #38bdf8;border-color:transparent}
.row{display:grid;grid-template-columns:1fr 1fr;gap:14px}
.srow{margin-bottom:18px}
.shdr{display:flex;justify-content:space-between;align-items:baseline;margin-bottom:6px}
.shdr label{margin:0}
.sval{font-size:.9rem;font-weight:700;color:#e2e8f0;background:#0f172a;
      border-radius:5px;padding:1px 8px;min-width:42px;text-align:center}
input[type=range]{-webkit-appearance:none;width:100%;height:6px;border-radius:3px;
      background:#334155;outline:none;cursor:pointer;margin:0;padding:0;border:none}
input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:18px;height:18px;
      border-radius:50%;background:#38bdf8;cursor:pointer}
input[type=range]::-moz-range-thumb{width:18px;height:18px;border-radius:50%;
      background:#38bdf8;cursor:pointer;border:none}
.checkrow{display:flex;align-items:center;gap:10px;margin:0 0 18px;
      padding:11px 12px;border:1px solid #334155;border-radius:8px;
      background:#0f172a}
.checkrow input{width:18px;height:18px;accent-color:#38bdf8}
.checkrow label{margin:0;color:#e2e8f0;text-transform:none;letter-spacing:0;
      font-size:.92rem}
button{width:100%;padding:12px;border-radius:8px;border:none;
       background:#0ea5e9;color:#fff;font-size:1rem;font-weight:600;
       cursor:pointer;transition:background .15s;margin-top:6px}
button:hover{background:#38bdf8}
button:active{background:#0284c7}
button:disabled{background:#334155;cursor:not-allowed}
.box{margin-top:22px;padding:14px;background:#0f172a;border-radius:8px;
     font-size:.82rem;color:#94a3b8;line-height:1.9}
.box span{color:#e2e8f0;font-weight:600}
.dot{display:inline-block;width:8px;height:8px;border-radius:50%;
     background:#22c55e;margin-right:6px;animation:pulse 2s infinite}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.35}}
.err{color:#f87171}
</style>
</head>
<body>
<div class="card">
  <h1>&#128225; ESP32 Radar Display</h1>
  <p class="sub">Center by ZIP, lat/lon, or SAME/NWS county code</p>

  <label for="center_mode">Map Center</label>
  <select id="center_mode" onchange="markDirty('center_mode');toggleCenterFields()">
    <option value="zip">ZIP Code</option>
    <option value="county">NWS County / SAME</option>
    <option value="latlon">Latitude / Longitude</option>
  </select>

  <div id="zipFields">
    <label for="zip">ZIP Code</label>
    <input id="zip" type="text" maxlength="5" pattern="[0-9]{5}" placeholder="e.g. 27587" oninput="markDirty('zip')">
    <p class="hint">US 5-digit ZIP code.</p>
  </div>

  <div id="countyFields">
    <label for="county_code">SAME / NWS County or Zone Code</label>
    <input id="county_code" type="text" maxlength="6" placeholder="e.g. 037183, NCC183, NCZ183" oninput="markDirty('county_code')">
    <p class="hint">Accepts 6-digit SAME, county codes like NCC183, or zone codes like NCZ183.</p>
  </div>

  <div class="row" id="latlonFields">
    <div>
      <label for="lat">Latitude</label>
      <input id="lat" type="number" min="-85" max="85" step="0.0001" placeholder="35.9799" oninput="markDirty('lat')">
    </div>
    <div>
      <label for="lon">Longitude</label>
      <input id="lon" type="number" min="-180" max="180" step="0.0001" placeholder="-78.5097" oninput="markDirty('lon')">
    </div>
  </div>
  <p class="hint" id="latlonHint">Decimal degrees. Use negative longitude for locations west of Greenwich.</p>

  <div class="row">
    <div>
      <label for="zoom">Zoom</label>
      <select id="zoom" onchange="markDirty('zoom')">
        <option value="5">5 ~ 500 km</option>
        <option value="6">6 ~ 250 km</option>
        <option value="7">7 ~ 125 km</option>
        <option value="8">8 ~  60 km</option>
        <option value="9">9 ~  30 km</option>
        <option value="10">10 ~ 15 km</option>
        <option value="11">11 ~  8 km</option>
        <option value="12">12 ~  4 km</option>
      </select>
    </div>
    <div>
      <label for="rotation">Rotation</label>
      <select id="rotation" onchange="markDirty('rotation')">
        <option value="0">0&deg; Portrait</option>
        <option value="1">90&deg; Landscape</option>
        <option value="2">180&deg; Inv. Portrait</option>
        <option value="3">270&deg; Inv. Landscape</option>
      </select>
    </div>
  </div>

  <label for="interval">Update Interval (seconds)</label>
  <input id="interval" type="number" min="30" max="3600" step="30" oninput="markDirty('interval')">

  <div class="srow">
    <div class="shdr">
      <label for="brightness">Map Brightness</label>
      <span class="sval" id="brightVal">1.00</span>
    </div>
    <input type="range" id="brightness" min="0.25" max="2.0" step="0.05" value="1.0"
           oninput="markDirty('brightness');document.getElementById('brightVal').textContent=parseFloat(this.value).toFixed(2)">
  </div>

  <div class="srow">
    <div class="shdr">
      <label for="radar_opacity">Radar Opacity</label>
      <span class="sval" id="opacityVal">1.00</span>
    </div>
    <input type="range" id="radar_opacity" min="0.0" max="1.0" step="0.05" value="1.0"
           oninput="markDirty('radar_opacity');document.getElementById('opacityVal').textContent=parseFloat(this.value).toFixed(2)">
  </div>

  <div class="checkrow">
    <input id="alert_polygons" type="checkbox" onchange="markDirty('alert_polygons')">
    <label for="alert_polygons">NWS warning/statement polygons</label>
  </div>

  <div class="srow">
    <div class="shdr">
      <label for="alert_fill_opacity">NWS Fill Opacity</label>
      <span class="sval" id="alertFillVal">0.25</span>
    </div>
    <input type="range" id="alert_fill_opacity" min="0.0" max="1.0" step="0.05" value="0.25"
           oninput="markDirty('alert_fill_opacity');document.getElementById('alertFillVal').textContent=parseFloat(this.value).toFixed(2)">
  </div>

  <button id="btn" onclick="apply()">&#9654; Apply &amp; Update Display Now</button>

  <div class="box" id="box"><div><span class="dot"></span>Loading...</div></div>
</div>

<script>
const dirtyFields=new Set();
function markDirty(id){
  dirtyFields.add(id);
}
function isDirty(id){
  return dirtyFields.has(id);
}
function toggleCenterFields(){
  const mode=document.getElementById('center_mode').value;
  document.getElementById('zipFields').style.display=(mode==='zip')?'block':'none';
  document.getElementById('countyFields').style.display=(mode==='county')?'block':'none';
  document.getElementById('latlonFields').style.display=(mode==='latlon')?'grid':'none';
  document.getElementById('latlonHint').style.display=(mode==='latlon')?'block':'none';
}
function setCenterFromStatus(d){
  const mode=d.center_mode||'zip';
  if(!isDirty('center_mode')) document.getElementById('center_mode').value=mode;
  if(!isDirty('zip')) document.getElementById('zip').value=d.zipcode||'';
  if(!isDirty('county_code')) document.getElementById('county_code').value=d.county_code||'';
  if(!isDirty('lat')) document.getElementById('lat').value=d.lat;
  if(!isDirty('lon')) document.getElementById('lon').value=d.lon;
  toggleCenterFields();
}
async function poll(){
  try{
    const d=await(await fetch('/api/status')).json();
    function setVal(id,val){
      const el=document.getElementById(id);
      if(el&&!isDirty(id)) el.value=val;
    }
    setCenterFromStatus(d);
    setVal('zoom',d.zoom);
    setVal('rotation',d.rotation);
    setVal('interval',d.interval);
    const alertEl=document.getElementById('alert_polygons');
    if(alertEl&&!isDirty('alert_polygons')) alertEl.checked=!!d.alert_polygons;
    const bv=parseFloat(d.brightness).toFixed(2);
    const ov=parseFloat(d.radar_opacity).toFixed(2);
    const av=parseFloat(d.alert_fill_opacity).toFixed(2);
    const brightEl=document.getElementById('brightness');
    const opacEl=document.getElementById('radar_opacity');
    const alertFillEl=document.getElementById('alert_fill_opacity');
    if(brightEl&&!isDirty('brightness')){
      brightEl.value=bv;
      document.getElementById('brightVal').textContent=bv;
    }
    if(opacEl&&!isDirty('radar_opacity')){
      opacEl.value=ov;
      document.getElementById('opacityVal').textContent=ov;
    }
    if(alertFillEl&&!isDirty('alert_fill_opacity')){
      alertFillEl.value=av;
      document.getElementById('alertFillVal').textContent=av;
    }
    const centerText=(d.center_mode==='zip'&&d.zipcode)
      ? 'ZIP <span>'+d.zipcode+'</span>'
      : (d.center_mode==='county'&&d.county_code)
        ? 'County <span>'+d.county_code+'</span> <span>'+d.lat+', '+d.lon+'</span>'
        : 'Lat/Lon <span>'+d.lat+', '+d.lon+'</span>';
    document.getElementById('box').innerHTML=
      '<div><span class="dot"></span>Status: <span>'+d.status+'</span></div>'+
      '<div>'+centerText+'</div>'+
      '<div>Zoom <span>'+d.zoom+'</span> &nbsp; Rotation <span>'+(d.rotation*90)+
      '&deg;</span> &nbsp; Interval <span>'+d.interval+'s</span></div>'+
      '<div>Brightness <span>'+bv+'</span> &nbsp; Radar Opacity <span>'+ov+'</span></div>'+
      '<div>NWS <span>'+(d.alert_polygons?'On':'Off')+
      '</span> &nbsp; NWS Fill <span>'+av+'</span></div>'+
      '<div>Frame <span>#'+d.frame+'</span> &nbsp; Last: <span>'+d.last_sent+'</span></div>';
  }catch(e){
    document.getElementById('box').innerHTML='<span class="err">Cannot reach server</span>';
  }
}
async function apply(){
  const btn=document.getElementById('btn');
  const mode=document.getElementById('center_mode').value;
  const payload={
    center_mode:mode,
    zoom:parseInt(document.getElementById('zoom').value),
    rotation:parseInt(document.getElementById('rotation').value),
    interval:parseInt(document.getElementById('interval').value),
    brightness:parseFloat(document.getElementById('brightness').value),
    radar_opacity:parseFloat(document.getElementById('radar_opacity').value),
    alert_polygons:document.getElementById('alert_polygons').checked,
    alert_fill_opacity:parseFloat(document.getElementById('alert_fill_opacity').value),
  };
  if(mode==='zip'){
    const zip=document.getElementById('zip').value.trim();
    if(!/^\d{5}$/.test(zip)){alert('Enter a valid 5-digit ZIP code');return;}
    payload.zipcode=zip;
  }else if(mode==='county'){
    const county=document.getElementById('county_code').value.trim().toUpperCase();
    if(!/^(\d{6}|[A-Z]{2}[CZ]\d{3})$/.test(county)){alert('Enter a 6-digit SAME code or NWS code like NCC183');return;}
    payload.county_code=county;
  }else{
    const lat=parseFloat(document.getElementById('lat').value);
    const lon=parseFloat(document.getElementById('lon').value);
    if(!Number.isFinite(lat)||lat<-85||lat>85){alert('Enter latitude from -85 to 85');return;}
    if(!Number.isFinite(lon)||lon<-180||lon>180){alert('Enter longitude from -180 to 180');return;}
    payload.lat=lat;
    payload.lon=lon;
  }
  btn.disabled=true; btn.textContent='Updating...';
  try{
    const r=await fetch('/api/update',{
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify(payload)
    });
    const d=await r.json();
    if(!d.ok) alert('Error: '+d.error);
    else{
      dirtyFields.clear();
      poll();
    }
  }catch(e){alert('Request failed: '+e);}
  btn.disabled=false; btn.textContent='▶ Apply & Update Display Now';
}
toggleCenterFields(); poll(); setInterval(poll,5000);
</script>
</body>
</html>
"""


def make_handler(state: RadarState, trigger: threading.Event):
    """Return a request-handler class closed over state + trigger."""

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):
            pass  # suppress default access log noise

        def _send_json(self, code, obj):
            body = json.dumps(obj).encode()
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            if urlparse(self.path).path == "/api/status":
                self._send_json(200, state.info())
                return
            body = _HTML.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def do_POST(self):
            if urlparse(self.path).path != "/api/update":
                self.send_response(404)
                self.end_headers()
                return
            length = int(self.headers.get("Content-Length", 0))
            try:
                data = json.loads(self.rfile.read(length))
            except Exception:
                self._send_json(400, {"ok": False, "error": "bad JSON"})
                return

            try:
                center_mode   = str(data.get("center_mode", "")).strip().lower()
                zipcode       = str(data.get("zipcode", "")).strip() or None
                county_code   = (str(data.get("county_code", "")).strip()
                                 or str(data.get("same", "")).strip()
                                 or str(data.get("county", "")).strip()
                                 or None)
                lat           = float(data["lat"])          if "lat"           in data else None
                lon           = float(data["lon"])          if "lon"           in data else None
                zoom          = int(data["zoom"])           if "zoom"          in data else None
                rotation      = int(data["rotation"])       if "rotation"      in data else None
                interval      = int(data["interval"])       if "interval"      in data else None
                brightness    = float(data["brightness"])   if "brightness"    in data else None
                radar_opacity = float(data["radar_opacity"]) if "radar_opacity" in data else None
                alert_polygons = (bool(data["alert_polygons"])
                                  if "alert_polygons" in data else None)
                alert_fill_opacity = (float(data["alert_fill_opacity"])
                                      if "alert_fill_opacity" in data else None)
            except Exception as e:
                self._send_json(400, {"ok": False, "error": f"bad value: {e}"})
                return

            if zoom is not None and not (5 <= zoom <= 12):
                self._send_json(400, {"ok": False, "error": "zoom must be 5-12"})
                return
            if rotation is not None and rotation not in (0, 1, 2, 3):
                self._send_json(400, {"ok": False, "error": "rotation must be 0-3"})
                return
            if interval is not None and not (30 <= interval <= 3600):
                self._send_json(400, {"ok": False, "error": "interval 30-3600"})
                return
            if brightness is not None and not (0.25 <= brightness <= 2.0):
                self._send_json(400, {"ok": False, "error": "brightness 0.25-2.0"})
                return
            if radar_opacity is not None and not (0.0 <= radar_opacity <= 1.0):
                self._send_json(400, {"ok": False, "error": "radar_opacity 0.0-1.0"})
                return
            if alert_fill_opacity is not None and not (0.0 <= alert_fill_opacity <= 1.0):
                self._send_json(400, {"ok": False, "error": "alert_fill_opacity 0.0-1.0"})
                return
            if center_mode == "zip":
                lat = None
                lon = None
                county_code = None
                if not zipcode:
                    self._send_json(400, {"ok": False, "error": "zipcode is required"})
                    return
            elif center_mode == "county":
                zipcode = None
                lat = None
                lon = None
                if not county_code:
                    self._send_json(400, {"ok": False, "error": "county_code is required"})
                    return
            elif center_mode == "latlon":
                zipcode = None
                county_code = None
                if lat is None or lon is None:
                    self._send_json(400, {"ok": False, "error": "lat and lon are required"})
                    return
                try:
                    validate_latlon(lat, lon)
                except Exception as e:
                    self._send_json(400, {"ok": False, "error": str(e)})
                    return
            elif zipcode:
                lat = None
                lon = None
                county_code = None
            elif county_code:
                lat = None
                lon = None
                zipcode = None
            elif lat is not None or lon is not None:
                if lat is None or lon is None:
                    self._send_json(400, {"ok": False, "error": "lat and lon are required"})
                    return
                try:
                    validate_latlon(lat, lon)
                except Exception as e:
                    self._send_json(400, {"ok": False, "error": str(e)})
                    return

            err = state.update(zipcode=zipcode, county_code=county_code,
                               zoom=zoom,
                               rotation=rotation, interval=interval,
                               lat=lat, lon=lon,
                               brightness=brightness,
                               radar_opacity=radar_opacity,
                               alert_polygons=alert_polygons,
                               alert_fill_opacity=alert_fill_opacity)
            if err:
                self._send_json(400, {"ok": False, "error": err})
                return

            trigger.set()   # wake the radar worker immediately
            self._send_json(200, {"ok": True})

    return Handler


def _coerce_bool(value):
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        v = value.strip().lower()
        if v in ("1", "true", "yes", "on"):
            return True
        if v in ("0", "false", "no", "off"):
            return False
    raise ValueError(f"invalid boolean {value!r}")


def parse_tcp_api_command(line: str) -> tuple[str, dict | None]:
    """
    Parse one TCP API command.

    Supported:
      status
      help
      {"zipcode":"27587","zoom":9}
      {"county_code":"NCC183","zoom":9}
      {"lat":35.9799,"lon":-78.5097,"zoom":9}
      zip=27587 zoom=9
      county=NCC183 zoom=9
      lat=35.9799 lon=-78.5097 zoom=9
    """
    text = line.strip()
    if not text:
        raise ValueError("empty command")
    lowered = text.lower()
    if lowered in ("help", "?"):
        return "help", None
    if lowered in ("status", "info"):
        return "status", None
    if text.startswith("{"):
        data = json.loads(text)
        if not isinstance(data, dict):
            raise ValueError("JSON command must be an object")
        return "update", data

    data = {}
    for token in text.replace(",", " ").split():
        if "=" not in token:
            raise ValueError(f"expected key=value token, got {token!r}")
        key, value = token.split("=", 1)
        key = key.strip().lower()
        value = value.strip()
        if key == "zip":
            key = "zipcode"
        elif key in ("same", "county"):
            key = "county_code"
        data[key] = value
    return "update", data


def apply_tcp_api_update(state: RadarState, data: dict) -> str:
    zipcode = str(data.get("zipcode", "")).strip() or None
    county_code = str(data.get("county_code", "")).strip() or None
    lat = float(data["lat"]) if "lat" in data else None
    lon = float(data["lon"]) if "lon" in data else None
    zoom = int(data["zoom"]) if "zoom" in data else None
    rotation = int(data["rotation"]) if "rotation" in data else None
    interval = int(data["interval"]) if "interval" in data else None
    brightness = float(data["brightness"]) if "brightness" in data else None
    radar_opacity = float(data["radar_opacity"]) if "radar_opacity" in data else None
    alert_polygons = (_coerce_bool(data["alert_polygons"])
                      if "alert_polygons" in data else None)
    alert_fill_opacity = (float(data["alert_fill_opacity"])
                          if "alert_fill_opacity" in data else None)

    if zoom is not None and not (5 <= zoom <= 12):
        raise ValueError("zoom must be 5-12")
    if rotation is not None and rotation not in (0, 1, 2, 3):
        raise ValueError("rotation must be 0-3")
    if interval is not None and not (30 <= interval <= 3600):
        raise ValueError("interval 30-3600")
    if brightness is not None and not (0.25 <= brightness <= 2.0):
        raise ValueError("brightness 0.25-2.0")
    if radar_opacity is not None and not (0.0 <= radar_opacity <= 1.0):
        raise ValueError("radar_opacity 0.0-1.0")
    if alert_fill_opacity is not None and not (0.0 <= alert_fill_opacity <= 1.0):
        raise ValueError("alert_fill_opacity 0.0-1.0")
    if zipcode and county_code:
        raise ValueError("use only one center: zipcode, county_code, or lat/lon")
    if zipcode:
        lat = None
        lon = None
    elif county_code:
        lat = None
        lon = None
    elif lat is not None or lon is not None:
        if lat is None or lon is None:
            raise ValueError("lat and lon must be provided together")
        validate_latlon(lat, lon)

    err = state.update(zipcode=zipcode, county_code=county_code,
                       zoom=zoom, rotation=rotation,
                       interval=interval, lat=lat, lon=lon,
                       brightness=brightness,
                       radar_opacity=radar_opacity,
                       alert_polygons=alert_polygons,
                       alert_fill_opacity=alert_fill_opacity)
    if err:
        raise ValueError(err)
    return "updated"


def tcp_api_client(conn: socket.socket, addr, state: RadarState,
                   trigger: threading.Event):
    with conn:
        conn.settimeout(300)
        conn.sendall(
            b"ESP32 radar API ready. Send JSON or key=value commands; help for examples.\n"
        )
        buf = b""
        while True:
            chunk = conn.recv(4096)
            if not chunk:
                return
            buf += chunk
            while b"\n" in buf:
                line, buf = buf.split(b"\n", 1)
                try:
                    command, data = parse_tcp_api_command(
                        line.decode("utf-8", errors="replace")
                    )
                    if command == "help":
                        reply = {
                            "ok": True,
                            "commands": [
                                "status",
                                "{\"zipcode\":\"27587\",\"zoom\":9}",
                                "{\"county_code\":\"NCC183\",\"zoom\":9}",
                                "{\"lat\":35.9799,\"lon\":-78.5097,\"zoom\":9}",
                                "zip=27587 zoom=9",
                                "county=NCC183 zoom=9",
                                "lat=35.9799 lon=-78.5097 zoom=9",
                            ],
                        }
                    elif command == "status":
                        reply = {"ok": True, "status": state.info()}
                    else:
                        apply_tcp_api_update(state, data or {})
                        trigger.set()
                        reply = {"ok": True, "status": state.info()}
                except Exception as e:
                    reply = {"ok": False, "error": str(e)}
                conn.sendall((json.dumps(reply) + "\n").encode("utf-8"))


def tcp_api_server(state: RadarState, trigger: threading.Event,
                   host: str, port: int):
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as server:
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server.bind((host, port))
        server.listen()
        while True:
            conn, addr = server.accept()
            threading.Thread(
                target=tcp_api_client,
                args=(conn, addr, state, trigger),
                daemon=True,
            ).start()


# ─────────────────────────────────────────────────────────────────────────────
# main()
# ─────────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="IEM NEXRAD radar → ESP32 TFT with live web control UI"
    )
    parser.add_argument("--zip",
                        help="Initial US ZIP code")
    parser.add_argument("--county",
                        help="Initial 6-digit SAME or NWS county/zone code, e.g. NCC183")
    parser.add_argument("--lat", type=float,
                        help="Initial center latitude")
    parser.add_argument("--lon", type=float,
                        help="Initial center longitude")
    parser.add_argument("--host",
                        help="ESP32 IP address for direct TCP mode")
    parser.add_argument("--port",     type=int, default=TCP_PORT,
                        help=f"ESP32 TCP port (default: {TCP_PORT})")
    parser.add_argument("--channel-server",
                        help="channel_server host; enables channel image transfer mode")
    parser.add_argument("--channel-port", type=int, default=9000,
                        help="channel_server TCP port (default: 9000)")
    parser.add_argument("--channel", default="radar",
                        help="display channel for image transfer mode (default: radar)")
    parser.add_argument("--control-channel", default="tft/control",
                        help="control channel to publish the channel list (default: tft/control)")
    parser.add_argument("--no-control", action="store_true",
                        help="do not publish the control channel list in channel mode")
    parser.add_argument("--interval", type=int, default=300,
                        help="Initial update interval in seconds (default: 300)")
    parser.add_argument("--zoom",     type=int, default=8,
                        choices=range(5, 13),
                        help="Initial map zoom 5-12 (default: 8)")
    parser.add_argument("--rotation", type=int, default=0,
                        choices=[0, 1, 2, 3],
                        help="Image rotation: 0=portrait 1=90 2=180 3=270 (default: 0)")
    parser.add_argument("--brightness",    type=float, default=1.0,
                        help="Base map brightness 0.25-2.0 (default: 1.0)")
    parser.add_argument("--radar-opacity", type=float, default=1.0,
                        dest="radar_opacity",
                        help="Radar overlay opacity 0.0-1.0 (default: 1.0)")
    parser.add_argument("--alert-polygons", action="store_true",
                        help="Start with NWS alert polygons enabled")
    parser.add_argument("--alert-fill-opacity", type=float,
                        default=NWS_ALERT_FILL_OPACITY,
                        help=("NWS alert polygon fill opacity 0.0-1.0 "
                              f"(default: {NWS_ALERT_FILL_OPACITY})"))
    parser.add_argument("--webport",  type=int, default=8080,
                        help="Web UI port (default: 8080)")
    parser.add_argument("--api-port", type=int, default=API_PORT,
                        help=f"TCP control API port (default: {API_PORT})")
    parser.add_argument("--api-bind", default="0.0.0.0",
                        help="TCP control API bind address (default: 0.0.0.0)")
    args = parser.parse_args()

    if not args.channel_server and not args.host:
        sys.exit("Either --host for direct TCP mode or --channel-server for channel mode is required")
    if not (0.0 <= args.alert_fill_opacity <= 1.0):
        sys.exit("--alert-fill-opacity must be between 0.0 and 1.0")
    initial_centers = sum([
        bool(args.zip),
        bool(args.county),
        args.lat is not None or args.lon is not None,
    ])
    if initial_centers > 1:
        sys.exit("Use only one initial center: --zip, --county, or --lat/--lon")
    if initial_centers == 0:
        sys.exit("Initial center required: use --zip, --county, or both --lat and --lon")

    if args.zip:
        print(f"Resolving ZIP {args.zip} ...")
        try:
            lat, lon = zip_to_latlon(args.zip)
        except Exception as e:
            sys.exit(f"ZIP lookup failed: {e}")
        zipcode = args.zip
        county_code = ""
    elif args.county:
        print(f"Resolving NWS county/SAME code {args.county} ...")
        try:
            lat, lon, county_code = nws_code_to_latlon(args.county)
        except Exception as e:
            sys.exit(f"NWS zone lookup failed: {e}")
        zipcode = ""
    else:
        if args.lat is None or args.lon is None:
            sys.exit("lat and lon must be provided together")
        lat, lon = args.lat, args.lon
        zipcode = ""
        county_code = ""
        try:
            validate_latlon(lat, lon)
        except Exception as e:
            sys.exit(str(e))
    print(f"  {lat:.4f}, {lon:.4f}")

    # Shared state + wakeup trigger
    state   = RadarState(zipcode, args.zoom, args.rotation,
                         args.interval, lat, lon,
                         county_code=county_code,
                         brightness=args.brightness,
                         radar_opacity=args.radar_opacity,
                         alert_polygons=args.alert_polygons,
                         alert_fill_opacity=args.alert_fill_opacity)
    trigger = threading.Event()

    if args.channel_server and not args.no_control:
        print(f"Publishing control channel list: [{args.channel!r}]")
        publish_control_channels(args.channel_server, args.channel_port,
                                 args.control_channel, [args.channel])
        time.sleep(0.35)

    # Radar worker (daemon so it dies when main exits)
    threading.Thread(
        target=radar_worker,
        args=(state, args.host, args.port, trigger,
              args.channel_server, args.channel_port, args.channel),
        daemon=True,
    ).start()

    threading.Thread(
        target=nws_alert_worker,
        args=(state, trigger),
        daemon=True,
    ).start()

    # Web server (daemon)
    httpd = HTTPServer(("0.0.0.0", args.webport), make_handler(state, trigger))
    threading.Thread(target=httpd.serve_forever, daemon=True).start()

    threading.Thread(
        target=tcp_api_server,
        args=(state, trigger, args.api_bind, args.api_port),
        daemon=True,
    ).start()

    # Discover the LAN IP so we can print a shareable URL
    try:
        lan_ip = socket.gethostbyname(socket.gethostname())
        # gethostbyname can return 127.0.0.1 on some systems; fall back
        if lan_ip.startswith("127."):
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(("8.8.8.8", 80))
            lan_ip = s.getsockname()[0]
            s.close()
    except Exception:
        lan_ip = "localhost"
    print(f"\nWeb UI (this machine) : http://localhost:{args.webport}")
    print(f"Web UI (network)      : http://{lan_ip}:{args.webport}")
    print(f"TCP control API       : {args.api_bind}:{args.api_port}")
    if args.channel_server:
        print(f"Channel image mode : {args.channel_server}:{args.channel_port}/{args.channel}")
    else:
        print(f"ESP32  : {args.host}:{args.port}")
    if args.zip:
        center_label = f"ZIP={args.zip}"
    elif args.county:
        center_label = f"County={county_code}"
    else:
        center_label = f"lat/lon={lat:.4f},{lon:.4f}"
    print(f"{center_label}  zoom={args.zoom}  "
          f"rotation={args.rotation}  interval={args.interval}s")
    print("Ctrl+C to exit\n")

    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("\nShutting down...")
        httpd.shutdown()


if __name__ == "__main__":
    main()
