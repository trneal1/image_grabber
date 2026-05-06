#!/usr/bin/env python3
"""
iem_radar_display.py

Fetches a live NEXRAD radar image centred on a ZIP code from the Iowa
Environmental Mesonet (IEM) and sends it to the ESP32 TFT display over TCP.
Repeats at a configurable interval.

Radar source : IEM NEXRAD N0Q CONUS Composite WMS
               https://mesonet.agron.iastate.edu/cgi-bin/wms/nexrad/n0q.cgi
               Free, no API key, no zoom limit, ~5 min updates.
               N0Q = 8-bit base reflectivity (higher resolution than N0R).
Map base     : OpenStreetMap tiles (any zoom)
Display      : raw RGB565 via the RGB! TCP protocol
               Header: MAGIC(4) + W(2BE) + H(2BE) + ROTATION(1) = 9 bytes
               Image is pre-rotated before sending; W×H match the rotation:
                 0=portrait 320×480  1=90° CW 480×320
                 2=180°     320×480  3=270° CW 480×320

Usage:
    python iem_radar_display.py --zip 27587 --host 192.168.1.42
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
MAGIC     = b"RGB!"

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

# ── Shared HTTP session ───────────────────────────────────────────────────────
_session = requests.Session()
_session.headers.update({"User-Agent": "ESP32-IEMRadar/1.0"})

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
                     crop_left: int, crop_top: int) -> tuple[float, float, float, float]:
    """
    Return (min_lat, min_lon, max_lat, max_lon) for the DISPLAY_W × DISPLAY_H
    crop window in WGS-84 degrees.  Used to build the WMS BBOX.
    """
    n = 2 ** z

    def px_to_lon(px: float) -> float:
        return (px / (n * TILE_SIZE) + tx0 / n) * 360.0 - 180.0

    def px_to_lat(py: float) -> float:
        merc = math.pi * (1 - 2 * (py / (n * TILE_SIZE) + ty0 / n))
        return math.degrees(math.atan(math.sinh(merc)))

    min_lon = px_to_lon(crop_left)
    max_lon = px_to_lon(crop_left + DISPLAY_W)
    max_lat = px_to_lat(crop_top)           # y increases downward
    min_lat = px_to_lat(crop_top + DISPLAY_H)
    return min_lat, min_lon, max_lat, max_lon


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
# Image composition
# ─────────────────────────────────────────────────────────────────────────────

def build_radar_image(lat: float, lon: float, zoom: int,
                      brightness: float = 1.0,
                      radar_opacity: float = 1.0) -> Image.Image:
    """
    Build a DISPLAY_W × DISPLAY_H composite:
      1. OSM base map (tiled, any zoom)
      2. IEM NEXRAD N0Q radar overlay (WMS bounding-box, any zoom, no cap)
      3. Yellow crosshair at ZIP centre
      4. Timestamp + source banner
    """
    # ── Tile grid ─────────────────────────────────────────────────────────
    cx_tile, cy_tile = deg2tile(lat, lon, zoom)
    tiles_x = math.ceil(DISPLAY_W / TILE_SIZE) + 2
    tiles_y = math.ceil(DISPLAY_H / TILE_SIZE) + 2
    tx0 = cx_tile - tiles_x // 2
    ty0 = cy_tile - tiles_y // 2
    canvas_w = tiles_x * TILE_SIZE
    canvas_h = tiles_y * TILE_SIZE

    print(f"  OSM grid {tiles_x}×{tiles_y} tiles at zoom {zoom}")

    # ── 1. OSM base ───────────────────────────────────────────────────────
    base = build_osm_canvas(zoom, tx0, ty0, tiles_x, tiles_y)

    # ── Crop window centred on ZIP ────────────────────────────────────────
    px, py = latlon_to_canvas_px(lat, lon, zoom, tx0, ty0)
    crop_left = int(px) - DISPLAY_W // 2
    crop_top  = int(py) - DISPLAY_H // 2
    crop_left = max(0, min(crop_left, canvas_w - DISPLAY_W))
    crop_top  = max(0, min(crop_top,  canvas_h - DISPLAY_H))

    # ── 2. IEM radar overlay ──────────────────────────────────────────────
    min_lat, min_lon, max_lat, max_lon = crop_bbox_latlon(
        zoom, tx0, ty0, crop_left, crop_top)

    print(f"  BBOX: {min_lat:.4f},{min_lon:.4f} → {max_lat:.4f},{max_lon:.4f}")
    print(f"  Fetching IEM NEXRAD N0Q …", end=" ", flush=True)

    radar_ok = False
    try:
        radar = fetch_iem_radar(min_lat, min_lon, max_lat, max_lon,
                                DISPLAY_W, DISPLAY_H)
        img = base.crop((crop_left, crop_top,
                         crop_left + DISPLAY_W, crop_top + DISPLAY_H))
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
                         crop_left + DISPLAY_W, crop_top + DISPLAY_H)
                        ).convert("RGB")
        if brightness != 1.0:
            img = ImageEnhance.Brightness(img).enhance(brightness)

    # ── 3. Crosshair ──────────────────────────────────────────────────────
    draw = ImageDraw.Draw(img)
    cx, cy = DISPLAY_W // 2, DISPLAY_H // 2
    arm = 12
    draw.line([(cx - arm, cy), (cx + arm, cy)], fill=(255, 255, 0), width=2)
    draw.line([(cx, cy - arm), (cx, cy + arm)], fill=(255, 255, 0), width=2)
    draw.ellipse([cx - arm, cy - arm, cx + arm, cy + arm],
                 outline=(255, 255, 0), width=1)

    # ── 4. Info banner ─────────────────────────────────────────────────────
    banner_h = 24
    banner = Image.new("RGBA", (DISPLAY_W, banner_h), (0, 0, 0, 190))
    img_rgba = img.convert("RGBA")
    img_rgba.alpha_composite(banner, dest=(0, DISPLAY_H - banner_h))
    img = img_rgba.convert("RGB")

    draw = ImageDraw.Draw(img)
    try:
        font = ImageFont.truetype(
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 13)
    except Exception:
        font = ImageFont.load_default()

    local_time = datetime.now().strftime("%m/%d %H:%M")
    status = "IEM N0Q" if radar_ok else "IEM N0Q (FAIL)"
    label = f"{status}  z{zoom}  {local_time}"
    draw.text((4, DISPLAY_H - banner_h + 5), label,
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
            # BGR565: blue in high bits, red in low bits
            v = ((b & 0xF8) << 8) | ((g & 0xFC) << 3) | (r >> 3)
            row[x * 2]     = (v >> 8) & 0xFF
            row[x * 2 + 1] =  v       & 0xFF
        rows.append(bytes(row))
    return rows


# ─────────────────────────────────────────────────────────────────────────────
# TCP send
# ─────────────────────────────────────────────────────────────────────────────

def send_to_display(host: str, port: int, img: Image.Image,
                    rotation: int = 0, timeout: int = 30) -> bool:
    w, h   = img.size
    rows   = image_to_rgb565_rows(img)
    header = MAGIC + struct.pack(">HHB", w, h, rotation)
    total  = w * h * 2

    print(f"  Connecting {host}:{port} …")
    try:
        sock = socket.create_connection((host, port), timeout=10)
    except OSError as e:
        print(f"  Connect failed: {e}")
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


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────


# ─────────────────────────────────────────────────────────────────────────────
# Shared state  (all access protected by a Lock)
# ─────────────────────────────────────────────────────────────────────────────

class RadarState:
    def __init__(self, zipcode, zoom, rotation, interval, lat, lon,
                 brightness=1.0, radar_opacity=1.0):
        self._lock        = threading.Lock()
        self.zipcode      = zipcode
        self.zoom         = zoom
        self.rotation     = rotation   # 0=portrait 1=landscape 2=180 3=270
        self.interval     = interval
        self.lat          = lat
        self.lon          = lon
        self.brightness   = brightness    # 0.5–2.0, 1.0 = no change
        self.radar_opacity = radar_opacity # 0.0–1.0, 1.0 = fully opaque
        self.status       = "Starting..."
        self.last_sent    = None
        self.frame        = 0

    def get(self):
        with self._lock:
            return (self.zipcode, self.zoom, self.rotation,
                    self.interval, self.lat, self.lon,
                    self.brightness, self.radar_opacity)

    def update(self, zipcode=None, zoom=None, rotation=None, interval=None,
               brightness=None, radar_opacity=None):
        """Update one or more fields.  Re-resolves ZIP if it changed.
        Returns an error string on failure, or None on success."""
        with self._lock:
            if zipcode and zipcode != self.zipcode:
                try:
                    lat, lon = zip_to_latlon(zipcode)
                except Exception as e:
                    return str(e)
                self.zipcode = zipcode
                self.lat     = lat
                self.lon     = lon
            if zoom          is not None: self.zoom          = zoom
            if rotation      is not None: self.rotation      = rotation
            if interval      is not None: self.interval      = interval
            if brightness    is not None: self.brightness    = brightness
            if radar_opacity is not None: self.radar_opacity = radar_opacity
        return None

    def set_status(self, msg):
        with self._lock:
            self.status = msg

    def info(self):
        with self._lock:
            return {
                "zipcode":      self.zipcode,
                "zoom":         self.zoom,
                "rotation":     self.rotation,
                "interval":     self.interval,
                "brightness":   round(self.brightness, 2),
                "radar_opacity": round(self.radar_opacity, 2),
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

def radar_worker(state: RadarState, esp_host: str, esp_port: int,
                 trigger: threading.Event):
    """Runs forever.  Wakes on trigger (immediate update) or interval timeout."""
    while True:
        zipcode, zoom, rotation, interval, lat, lon, brightness, radar_opacity = state.get()

        state.set_status("Fetching radar...")
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        print(f"\n-- Frame {state.frame + 1}  {ts} --")
        print(f"   ZIP={zipcode}  zoom={zoom}  rotation={rotation}  "
              f"bright={brightness:.2f}  opacity={radar_opacity:.2f}")

        try:
            img = build_radar_image(lat, lon, zoom,
                                    brightness=brightness,
                                    radar_opacity=radar_opacity)
            if rotation == 1:
                img = img.rotate(90,  expand=True)
            elif rotation == 2:
                img = img.rotate(180, expand=True)
            elif rotation == 3:
                img = img.rotate(270, expand=True)
        except Exception as e:
            print(f"   Build failed: {e}")
            state.set_status(f"Error: {e}")
            trigger.wait(timeout=interval)
            trigger.clear()
            continue

        state.set_status("Sending to display...")
        ok = send_to_display(esp_host, esp_port, img, rotation=rotation)

        with state._lock:
            state.frame    += 1
            state.last_sent = datetime.now()
            state.status    = "OK" if ok else "Send failed"

        print(f"   Next in {interval}s (or on web change)")
        trigger.wait(timeout=interval)
        trigger.clear()


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
  <h1>&#127929; ESP32 Radar Display</h1>
  <p class="sub">IEM NEXRAD N0Q &mdash; changes update the display immediately</p>

  <label for="zip">ZIP Code</label>
  <input id="zip" type="text" maxlength="5" pattern="[0-9]{5}" placeholder="e.g. 27587">

  <div class="row">
    <div>
      <label for="zoom">Zoom</label>
      <select id="zoom">
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
      <select id="rotation">
        <option value="0">0&deg; Portrait</option>
        <option value="1">90&deg; Landscape</option>
        <option value="2">180&deg; Inv. Portrait</option>
        <option value="3">270&deg; Inv. Landscape</option>
      </select>
    </div>
  </div>

  <label for="interval">Update Interval (seconds)</label>
  <input id="interval" type="number" min="30" max="3600" step="30">

  <div class="srow">
    <div class="shdr">
      <label for="brightness">Map Brightness</label>
      <span class="sval" id="brightVal">1.00</span>
    </div>
    <input type="range" id="brightness" min="0.25" max="2.0" step="0.05" value="1.0"
           oninput="document.getElementById('brightVal').textContent=parseFloat(this.value).toFixed(2)">
  </div>

  <div class="srow">
    <div class="shdr">
      <label for="radar_opacity">Radar Opacity</label>
      <span class="sval" id="opacityVal">1.00</span>
    </div>
    <input type="range" id="radar_opacity" min="0.0" max="1.0" step="0.05" value="1.0"
           oninput="document.getElementById('opacityVal').textContent=parseFloat(this.value).toFixed(2)">
  </div>

  <button id="btn" onclick="apply()">&#9654; Apply &amp; Update Display Now</button>

  <div class="box" id="box"><div><span class="dot"></span>Loading...</div></div>
</div>

<script>
async function poll(){
  try{
    const d=await(await fetch('/api/status')).json();
    const active=document.activeElement;
    // Only update a field if the user is not currently editing it
    function setVal(id,val){
      const el=document.getElementById(id);
      if(el&&el!==active) el.value=val;
    }
    setVal('zip',d.zipcode);
    setVal('zoom',d.zoom);
    setVal('rotation',d.rotation);
    setVal('interval',d.interval);
    const bv=parseFloat(d.brightness).toFixed(2);
    const ov=parseFloat(d.radar_opacity).toFixed(2);
    // Sliders: skip update while user is dragging (focus check)
    const brightEl=document.getElementById('brightness');
    const opacEl=document.getElementById('radar_opacity');
    if(brightEl&&brightEl!==active){
      brightEl.value=bv;
      document.getElementById('brightVal').textContent=bv;
    }
    if(opacEl&&opacEl!==active){
      opacEl.value=ov;
      document.getElementById('opacityVal').textContent=ov;
    }
    document.getElementById('box').innerHTML=
      '<div><span class="dot"></span>Status: <span>'+d.status+'</span></div>'+
      '<div>ZIP <span>'+d.zipcode+'</span> &nbsp;<span style="font-size:.75rem;'+
      'background:#334155;border-radius:4px;padding:1px 6px">'+d.lat+', '+d.lon+'</span></div>'+
      '<div>Zoom <span>'+d.zoom+'</span> &nbsp; Rotation <span>'+(d.rotation*90)+
      '&deg;</span> &nbsp; Interval <span>'+d.interval+'s</span></div>'+
      '<div>Brightness <span>'+bv+'</span> &nbsp; Radar Opacity <span>'+ov+'</span></div>'+
      '<div>Frame <span>#'+d.frame+'</span> &nbsp; Last: <span>'+d.last_sent+'</span></div>';
  }catch(e){
    document.getElementById('box').innerHTML='<span class="err">Cannot reach server</span>';
  }
}
async function apply(){
  const btn=document.getElementById('btn');
  const zip=document.getElementById('zip').value.trim();
  if(!/^\d{5}$/.test(zip)){alert('Enter a valid 5-digit ZIP code');return;}
  btn.disabled=true; btn.textContent='Updating...';
  try{
    const r=await fetch('/api/update',{
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({
        zipcode:zip,
        zoom:parseInt(document.getElementById('zoom').value),
        rotation:parseInt(document.getElementById('rotation').value),
        interval:parseInt(document.getElementById('interval').value),
        brightness:parseFloat(document.getElementById('brightness').value),
        radar_opacity:parseFloat(document.getElementById('radar_opacity').value),
      })
    });
    const d=await r.json();
    if(!d.ok) alert('Error: '+d.error);
    else poll();
  }catch(e){alert('Request failed: '+e);}
  btn.disabled=false; btn.textContent='▶ Apply & Update Display Now';
}
poll(); setInterval(poll,5000);
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

            zipcode       = str(data.get("zipcode", "")).strip() or None
            zoom          = int(data["zoom"])           if "zoom"          in data else None
            rotation      = int(data["rotation"])       if "rotation"      in data else None
            interval      = int(data["interval"])       if "interval"      in data else None
            brightness    = float(data["brightness"])   if "brightness"    in data else None
            radar_opacity = float(data["radar_opacity"]) if "radar_opacity" in data else None

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

            err = state.update(zipcode=zipcode, zoom=zoom,
                               rotation=rotation, interval=interval,
                               brightness=brightness, radar_opacity=radar_opacity)
            if err:
                self._send_json(400, {"ok": False, "error": err})
                return

            trigger.set()   # wake the radar worker immediately
            self._send_json(200, {"ok": True})

    return Handler


# ─────────────────────────────────────────────────────────────────────────────
# main()
# ─────────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="IEM NEXRAD radar → ESP32 TFT with live web control UI"
    )
    parser.add_argument("--zip",      required=True,
                        help="Initial US ZIP code")
    parser.add_argument("--host",     required=True,
                        help="ESP32 IP address")
    parser.add_argument("--port",     type=int, default=TCP_PORT,
                        help=f"ESP32 TCP port (default: {TCP_PORT})")
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
    parser.add_argument("--webport",  type=int, default=8080,
                        help="Web UI port (default: 8080)")
    args = parser.parse_args()

    # Resolve initial ZIP
    print(f"Resolving ZIP {args.zip} ...")
    try:
        lat, lon = zip_to_latlon(args.zip)
    except Exception as e:
        sys.exit(f"ZIP lookup failed: {e}")
    print(f"  {lat:.4f}, {lon:.4f}")

    # Shared state + wakeup trigger
    state   = RadarState(args.zip, args.zoom, args.rotation,
                         args.interval, lat, lon,
                         brightness=args.brightness,
                         radar_opacity=args.radar_opacity)
    trigger = threading.Event()

    # Radar worker (daemon so it dies when main exits)
    threading.Thread(
        target=radar_worker,
        args=(state, args.host, args.port, trigger),
        daemon=True,
    ).start()

    # Web server (daemon)
    httpd = HTTPServer(("0.0.0.0", args.webport), make_handler(state, trigger))
    threading.Thread(target=httpd.serve_forever, daemon=True).start()

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
    print(f"ESP32  : {args.host}:{args.port}")
    print(f"ZIP={args.zip}  zoom={args.zoom}  "
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
