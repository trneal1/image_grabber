/*
 * tft_png_display.ino
 *
 * ESP32 WiFi Station + TCP server
 * Receives a raw RGB565 image (320x480) over TCP and renders it directly
 * to a ST7796S SPI TFT via Adafruit_GFX on the HSPI bus.
 *
 * No large heap buffer is required.  The Python sender converts any source
 * image to raw RGB565 in RGB order before sending, so the ESP32 only needs one
 * scanline of RAM at a time (~640 bytes for a 320-px-wide row).
 *
 * ── Protocol ────────────────────────────────────────────────────────────────
 *  Python → ESP32
 *    [4 bytes] magic    : 'R' 'G' 'B' '!'  (0x52 0x47 0x42 0x21)
 *    [2 bytes] width    : big-endian uint16
 *    [2 bytes] height   : big-endian uint16
 *    [1 byte]  rotation : 0=portrait  1=90° CW  2=180°  3=270° CW
 *    [W*H*2 bytes]      : raw RGB565, big-endian, row-major, top-to-bottom
 *                         Sender should pack pixels in RGB order:
 *                         red high bits, green middle bits, blue low bits.
 *                         Image is pre-rotated by sender; W×H match rotation.
 *
 *  ESP32 → Python
 *    "OK\n"   – image displayed
 *    "ERR\n"  – bad magic, wrong size, bad rotation, or timeout
 *
 * ── Libraries (install via Arduino Library Manager) ─────────────────────────
 *    Adafruit GFX Library              by Adafruit
 *    Adafruit ST7735 and ST7789 Library by Adafruit  (contains Adafruit_ST7796S)
 *
 * ── HSPI wiring ─────────────────────────────────────────────────────────────
 *    ST7796S          ESP32 (HSPI)
 *    --------         ------------
 *    MOSI     →       GPIO 13   (HSPI MOSI)
 *    SCLK     →       GPIO 14   (HSPI CLK)
 *    CS       →       GPIO 15   (HSPI CS0)
 *    DC       →       GPIO 12
 *    RST      →       GPIO 26
 *    BL       →       GPIO 27   (backlight; HIGH = on)
 *    VCC      →       3.3 V
 *    GND      →       GND
 *
 *  Note: GPIO 12 is a strapping pin on ESP32. If your module won't boot,
 *  move DC to GPIO 2 or 25 and update PIN_TFT_DC below.
 */

#include <SPI.h>
#include <WiFi.h>
#include <Adafruit_GFX.h>
#include <Adafruit_ST7796S.h>

// ── User configuration ───────────────────────────────────────────────────────
#define WIFI_SSID       "TRNNET-2G"
#define WIFI_PASSWORD   "ripcord1"
#define TCP_PORT        5555

// HSPI bus pin assignments (ESP32 HSPI = SPI2)
#define PIN_TFT_MOSI    13    // HSPI MOSI
#define PIN_TFT_SCLK    14    // HSPI CLK
#define PIN_TFT_CS      15    // HSPI CS0
#define PIN_TFT_DC      2    // Data/Command  (move to GPIO 2 if boot issues)
#define PIN_TFT_RST     -1    // Reset
#define PIN_TFT_BL      27    // Backlight LED (active HIGH; -1 to disable)

// Physical display dimensions (portrait)
#define IMG_WIDTH       320
#define IMG_HEIGHT      480
// Max row width across all rotations (landscape = 480 wide)
#define MAX_IMG_DIM     480

// Receive timeout, reset on each successful chunk read
#define RECV_TIMEOUT_MS  15000
// WiFi health check / reconnect timing
#define WIFI_CHECK_INTERVAL_MS    5000
#define WIFI_RECONNECT_TIMEOUT_MS 20000
// Refresh the TCP listener periodically; this helps recover from rare ESP32
// WiFiServer stalls where WiFi still reports connected but SYNs time out.
#define SERVER_REFRESH_INTERVAL_MS 30000
// ─────────────────────────────────────────────────────────────────────────────

static const uint8_t MAGIC[4] = {'R', 'G', 'B', '!'};

#define COLOR_BLACK  0x0000
#define COLOR_WHITE  0xFFFF
#define COLOR_CYAN   0x07FF

// ── HSPI + display ────────────────────────────────────────────────────────────
SPIClass         hspi(HSPI);
Adafruit_ST7796S tft(&hspi, PIN_TFT_CS, PIN_TFT_DC, PIN_TFT_RST);
WiFiServer       server(TCP_PORT);
static bool      serverStarted = false;
static uint32_t  lastWiFiCheck = 0;
static uint32_t  lastServerRefresh = 0;

// ── Scanline receive buffer ───────────────────────────────────────────────────
// One row at a time; up to MAX_IMG_DIM (480) pixels × 2 bytes = 960 bytes.
// Global to avoid living on the loop() task stack.
static uint16_t rowBuf[MAX_IMG_DIM];

// ── Helpers ───────────────────────────────────────────────────────────────────

bool tcpReadExact(WiFiClient& client, uint8_t* dst, uint32_t len)
{
    uint32_t deadline = millis() + RECV_TIMEOUT_MS;
    uint32_t got = 0;
    while (got < len) {
        if (!client.connected() || millis() > deadline) return false;
        int avail = client.available();
        if (avail <= 0) { delay(1); continue; }
        uint32_t want  = len - got;
        uint32_t chunk = ((uint32_t)avail < want) ? (uint32_t)avail : want;
        client.readBytes(dst + got, chunk);
        got += chunk;
        deadline = millis() + RECV_TIMEOUT_MS;
    }
    return true;
}

void showStatus(const char* line1, const char* line2 = nullptr)
{
    tft.fillScreen(COLOR_BLACK);
    tft.setTextColor(COLOR_WHITE);
    tft.setTextSize(2);
    tft.setCursor(4, 8);
    tft.print(line1);
    if (line2) { tft.setCursor(4, 32); tft.print(line2); }
}

void startTcpServer()
{
    server.begin();
    server.setNoDelay(true);
    serverStarted = true;
    lastServerRefresh = millis();
    Serial.printf("TCP server ready on port %d\n", TCP_PORT);
}

bool connectWiFi(uint32_t timeoutMs)
{
    Serial.printf("Connecting to %s\n", WIFI_SSID);
    WiFi.disconnect(false);
    delay(100);
    WiFi.begin(WIFI_SSID, WIFI_PASSWORD);

    uint32_t start = millis();
    uint8_t dots = 0;
    while (WiFi.status() != WL_CONNECTED && millis() - start < timeoutMs) {
        delay(500);
        Serial.print('.');
        tft.setCursor(4 + (dots % 14) * 12, 32);
        tft.print('.');
        dots++;
    }

    if (WiFi.status() != WL_CONNECTED) {
        Serial.println("\nWiFi connect timed out");
        return false;
    }

    String ip = WiFi.localIP().toString();
    Serial.printf("\nIP: %s\n", ip.c_str());
    Serial.printf("Free heap after WiFi: %u bytes\n", ESP.getFreeHeap());
    return true;
}

bool ensureWiFiConnected()
{
    if (WiFi.status() == WL_CONNECTED) {
        if (!serverStarted) startTcpServer();
        uint32_t now = millis();
        if (now - lastServerRefresh >= SERVER_REFRESH_INTERVAL_MS) {
            Serial.println("Refreshing TCP listener");
            startTcpServer();
        }
        return true;
    }

    uint32_t now = millis();
    if (now - lastWiFiCheck < WIFI_CHECK_INTERVAL_MS) return false;
    lastWiFiCheck = now;

    serverStarted = false;
    Serial.println("WiFi disconnected; reconnecting");
    showStatus("WiFi lost", "Reconnecting...");

    if (!connectWiFi(WIFI_RECONNECT_TIMEOUT_MS)) {
        showStatus("WiFi reconnect", "failed");
        return false;
    }

    startTcpServer();

    String ip = WiFi.localIP().toString();
    char portStr[20];
    snprintf(portStr, sizeof(portStr), "Port %d", TCP_PORT);
    showStatus(ip.c_str(), portStr);
    return true;
}

// ── setup() ──────────────────────────────────────────────────────────────────
void setup()
{
    Serial.begin(115200);
    delay(200);
    Serial.println("\n=== ESP32 TFT RGB565 Display (ST7796S) ===");
    Serial.printf("Free heap at boot: %u bytes\n", ESP.getFreeHeap());

    // ── Backlight ─────────────────────────────────────────────────────────
    if (PIN_TFT_BL >= 0) {
        pinMode(PIN_TFT_BL, OUTPUT);
        digitalWrite(PIN_TFT_BL, HIGH);
    }

    // ── HSPI + display ────────────────────────────────────────────────────
    hspi.begin(PIN_TFT_SCLK, /*MISO*/-1, PIN_TFT_MOSI, PIN_TFT_CS);
    tft.init(IMG_WIDTH, IMG_HEIGHT, 0, 0, ST7796S_BGR);
    tft.invertDisplay(true);
    tft.setRotation(0);
    tft.fillScreen(COLOR_BLACK);

    tft.setTextColor(COLOR_CYAN);
    tft.setTextSize(2);
    tft.setCursor(4, 8);
    tft.print("Connecting WiFi");

    // ── WiFi ──────────────────────────────────────────────────────────────
    WiFi.mode(WIFI_STA);
    WiFi.setSleep(false);
    WiFi.setAutoReconnect(true);
    while (!connectWiFi(WIFI_RECONNECT_TIMEOUT_MS)) {
        showStatus("WiFi failed", "Retrying...");
        delay(2000);
    }

    // ── TCP server ────────────────────────────────────────────────────────
    startTcpServer();

    String ip = WiFi.localIP().toString();
    char portStr[20];
    snprintf(portStr, sizeof(portStr), "Port %d", TCP_PORT);
    showStatus(ip.c_str(), portStr);
}

// ── loop() ───────────────────────────────────────────────────────────────────
void loop()
{
    if (!ensureWiFiConnected()) {
        delay(50);
        return;
    }

    WiFiClient client = server.accept();
    if (!client) {
        delay(5);
        return;
    }
    client.setNoDelay(true);

    String remoteIP = client.remoteIP().toString();
    Serial.printf("\nClient: %s\n", remoteIP.c_str());
    showStatus("Receiving...", remoteIP.c_str());

    // ── 1. Magic ──────────────────────────────────────────────────────────
    uint8_t magic[4] = {0};
    if (!tcpReadExact(client, magic, 4) || memcmp(magic, MAGIC, 4) != 0) {
        Serial.println("ERR: bad magic");
        client.print("ERR\n"); client.stop();
        showStatus("ERR: bad magic");
        return;
    }

    // ── 2. Dimensions + rotation (W:2, H:2, rot:1 bytes) ────────────────
    uint8_t hdrBuf[5] = {0};
    if (!tcpReadExact(client, hdrBuf, 5)) {
        Serial.println("ERR: timeout reading header");
        client.print("ERR\n"); client.stop();
        showStatus("ERR: timeout");
        return;
    }
    uint16_t imgW    = ((uint16_t)hdrBuf[0] << 8) | hdrBuf[1];
    uint16_t imgH    = ((uint16_t)hdrBuf[2] << 8) | hdrBuf[3];
    uint8_t  imgRot  = hdrBuf[4];
    Serial.printf("Image: %u x %u  rot=%u\n", imgW, imgH, imgRot);

    if (imgW == 0 || imgW > MAX_IMG_DIM || imgH == 0 || imgH > MAX_IMG_DIM) {
        Serial.printf("ERR: dimensions %ux%u out of range\n", imgW, imgH);
        client.print("ERR\n"); client.stop();
        showStatus("ERR: bad size");
        return;
    }
    if (imgRot > 3) {
        Serial.printf("ERR: invalid rotation %u\n", imgRot);
        client.print("ERR\n"); client.stop();
        showStatus("ERR: bad rot");
        return;
    }
    tft.setRotation(imgRot);

    // ── 3. Stream rows directly to the display ────────────────────────────
    // Each row: imgW × 2 bytes, big-endian RGB565 in RGB order.
    // We receive one row, byte-swap to little-endian, and blit immediately.
    // Peak extra RAM used: 640 bytes (rowBuf). No bulk buffer needed.
    for (uint16_t y = 0; y < imgH; y++) {

        if (!tcpReadExact(client, (uint8_t*)rowBuf, (uint32_t)imgW * 2)) {
            Serial.printf("ERR: timeout on row %u\n", y);
            client.print("ERR\n"); client.stop();
            showStatus("ERR: row timeout");
            return;
        }

        // Network byte order (big-endian) → Adafruit_GFX (little-endian)
        for (uint16_t x = 0; x < imgW; x++) {
            uint16_t px = rowBuf[x];
            rowBuf[x]   = (uint16_t)((px >> 8) | (px << 8));
        }

        tft.drawRGBBitmap(0, (int16_t)y, rowBuf, imgW, 1);
    }

    // ── 4. Acknowledge ────────────────────────────────────────────────────
    client.print("OK\n");
    client.stop();
    Serial.println("Image displayed OK");
}
