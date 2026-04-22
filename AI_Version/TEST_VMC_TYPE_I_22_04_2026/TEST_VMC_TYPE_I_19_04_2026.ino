#include <WiFi.h>
#include <Wire.h>
#include <LiquidCrystal_PCF8574.h>
#include <Preferences.h>
#include <HTTPClient.h>
#include "time.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include <ArduinoJson.h>
#include <WiFiClientSecure.h>
#include <vector>
#include <math.h>
#include "esp_system.h"

std::vector<String> payloadBuffer;
SemaphoreHandle_t bufferMutex;

LiquidCrystal_PCF8574 lcd(0x27); 
Preferences preferences;

const char* ntpServer = "pool.ntp.org";
const long gmtOffset_sec = 19800;
const int daylightOffset_sec = 0;

int idle = 0;
int shot_count = 0;
String deviceID;


bool count_flag=false;
bool send_flag=true;
bool showRSSI = false;
bool plan_req=true;
bool whatsapp_req = false;
bool whatsapp_sent = false;
String req_datetime;
String supervisor;
String payload_req;
time_t lastShotEpoch = 0;
bool idle45Sent = false;
volatile bool restartRequested = false;
volatile bool restartAckReceived = false;
static bool g_safe_restart_in_progress = false;
volatile uint8_t g_scheduled_safe_restart_slot = 0;
static bool g_this_boot_scheduled_clean = false;
bool restart_flag;
bool last_idle_sent =true;


unsigned long lastDebounceTimeBreak = 0;
unsigned long lastDebounceTimeSetting = 0;
unsigned long lastDebounceTimeMaintenance = 0;
unsigned long lastDebounceTimeManPower = 0;
unsigned long lastDebounceTimeNoload = 0;
unsigned long lastDebounceTimePowercut = 0;
unsigned long lastDebounceTimeToolChange = 0;

unsigned long debounceDelay = 30;

int lastBreakButtonState = LOW;
int lastSettingButtonState = LOW;
int lastMaintenanceButtonState = LOW;
int lastManPowerButtonState = LOW;
int lastNoloadButtonState = LOW;
int lastPowercutButtonState = LOW;
int lastToolChangeButtonState = LOW;

int breakButtonState;
int settingButtonState;
int maintenanceButtonState;
int ManPowerButtonState;
int noloadButtonState;
int powercutButtonState;
int ToolChangeButtonState;
bool wifi_check;

unsigned long lastLcdUpdate = 0;
unsigned long lcdUpdateInterval = 500;

bool resetDone = false;
static uint64_t g_schedrst_last_fire_id = 0;
static uint32_t g_sched_rst_write_ms = 0;
static uint32_t g_sched_fallback_restart_ms = 0;

unsigned long previousMillis = 0;
const unsigned long interval = 20000;

String partNo;
String itemCode;
String productionPlan;
SemaphoreHandle_t planMutex;

/** Same NVS keys as TEST_PDC — required for meas 46 `scheduled_*_ok` and safe restart ack. */
#define PDC_PREF_SCHED_RST_PEND "sched_rst_pend"
#define PDC_PREF_SCHED_MORN_RST "sched_morn_rst"
#define PDC_PREF_SCHED_EVE_RST "sched_eve_rst"
#define PDC_PREF_SCHED_MORN_RBT "sched_morn_rbt"
#define PDC_PREF_SCHED_EVE_RBT "sched_eve_rbt"
#define PDC_PREF_SCHED_RST_DAY "sched_rst_day"
#define PDC_PREF_SCHED_RST_SLOT "sched_rst_slot"

#ifndef VMC_HEALTH_PUBSUB_PUSH_INTERVAL_MS
#define VMC_HEALTH_PUBSUB_PUSH_INTERVAL_MS 600000
#endif
#ifndef VMC_HEALTH_QUEUE_TASK_STACK
#define VMC_HEALTH_QUEUE_TASK_STACK 12288
#endif

/** Shot-to-shot gap stats (same EWMA / abnormal rule as TEST_PDC); updated only when a shot is counted. */
static unsigned long g_last_shot_millis = 0;
static uint32_t g_last_cycle_duration_ms = 0;
static uint32_t g_cycle_time_ms_ewma = 0;
static bool g_abnormal_cycle = false;

static uint32_t g_loop_time_us_max = 0;
static uint32_t g_loop_time_us_avg = 0;
static unsigned long g_last_loop_end_ms = 0;

static volatile bool g_i2c_lcd_present = true;
static volatile uint32_t g_i2c_lcd_probe_fail_count = 0;
static unsigned long g_last_i2c_probe_ms = 0;

//----------------------------------------Type - I Variables-----------------------------------------------//
int low_count = 0;
int high_count = 0;
unsigned long start_time = 0;
unsigned long stop_time = 0;
bool high_flag = false;
//-----------------------------------------------------------------------------------------------------------//



#define WIFI_CONNECT_TIMEOUT 10000  

struct WiFiNetwork {
    String ssid;
    int rssi;
};


bool isTimeValid() {
    time_t now = time(nullptr);

    // Jan 1 2023 epoch ~ 1672531200
    // Anything less means NTP not synced
    if (now > 1672531200) {
        return true;
    }
    return false;
}

static inline void pdcPrefsPutUInt(const char* key, uint32_t val) {
  preferences.putUInt(key, val);
}

static inline void pdcPrefsPutULong64(const char* key, uint64_t val) {
  preferences.putULong64(key, val);
}

static uint32_t pdcLocalCalendarTag(const struct tm* ti) {
  if (!ti) return 0;
  return (uint32_t)(ti->tm_year + 1900) * 10000u + (uint32_t)(ti->tm_mon + 1) * 100u +
         (uint32_t)ti->tm_mday;
}

/** Dashboard daily flags (same semantics as TEST_PDC health meas 46). */
static void pdcScheduledResetSlotsForTelemetry(uint8_t* m_reset_ok, uint8_t* m_restart_ok, uint8_t* e_reset_ok,
                                                uint8_t* e_restart_ok) {
  *m_reset_ok = *m_restart_ok = *e_reset_ok = *e_restart_ok = 0;
  if (!isTimeValid()) return;
  time_t now = time(nullptr);
  struct tm* ti = localtime(&now);
  if (!ti) return;
  uint32_t tag = pdcLocalCalendarTag(ti);
  if (preferences.getUInt(PDC_PREF_SCHED_MORN_RST, 0) == tag) *m_reset_ok = 1;
  if (preferences.getUInt(PDC_PREF_SCHED_MORN_RBT, 0) == tag) *m_restart_ok = 1;
  if (preferences.getUInt(PDC_PREF_SCHED_EVE_RST, 0) == tag) *e_reset_ok = 1;
  if (preferences.getUInt(PDC_PREF_SCHED_EVE_RBT, 0) == tag) *e_restart_ok = 1;
}

static void pdcAckScheduledRestartFromNvs(void) {
  uint32_t pending = preferences.getUInt(PDC_PREF_SCHED_RST_PEND, 0);
  if (!pending) return;
  uint32_t dayTag = preferences.getUInt(PDC_PREF_SCHED_RST_DAY, 0);
  uint32_t slot = preferences.getUInt(PDC_PREF_SCHED_RST_SLOT, 0);
  esp_reset_reason_t rr = esp_reset_reason();
  bool ok = (rr == ESP_RST_SW);
  preferences.putUInt(PDC_PREF_SCHED_RST_PEND, 0);
  if (ok && dayTag != 0) {
    if (slot == 0)
      pdcPrefsPutUInt(PDC_PREF_SCHED_MORN_RBT, dayTag);
    else
      pdcPrefsPutUInt(PDC_PREF_SCHED_EVE_RBT, dayTag);
    g_this_boot_scheduled_clean = true;
  } else {
    pdcPrefsPutUInt(PDC_PREF_SCHED_RST_DAY, 0);
    pdcPrefsPutUInt(PDC_PREF_SCHED_RST_SLOT, 0);
  }
}

static void pdcPersistSessCountersNvs(void) {}

static void pdcApplyBootSessionCountersFromNvs(void) {
  (void)g_this_boot_scheduled_clean;
}

static void pdcMigrateLegacySchedNvs(void) {
  uint32_t m = preferences.getUInt("sched_morn_day", 0);
  if (m != 0 && preferences.getUInt(PDC_PREF_SCHED_MORN_RBT, 0) == 0) {
    pdcPrefsPutUInt(PDC_PREF_SCHED_MORN_RBT, m);
    preferences.remove("sched_morn_day");
  }
  uint32_t e = preferences.getUInt("sched_eve_day", 0);
  if (e != 0 && preferences.getUInt(PDC_PREF_SCHED_EVE_RBT, 0) == 0) {
    pdcPrefsPutUInt(PDC_PREF_SCHED_EVE_RBT, e);
    preferences.remove("sched_eve_day");
  }
}

static void pdcMaybeScheduledRestart(void) {
  if (!isTimeValid()) return;
  if (restartRequested) return;
  const uint32_t mnow = millis();
  if (mnow - g_sched_fallback_restart_ms < 60000UL) return;
  time_t now = time(nullptr);
  struct tm* ti = localtime(&now);
  if (!ti) return;
  uint32_t dayTag = pdcLocalCalendarTag(ti);
  const bool can_hard_fallback =
      (g_sched_rst_write_ms != 0 && (mnow - g_sched_rst_write_ms > 120000UL)) ||
      (g_sched_rst_write_ms == 0 && millis() > 120000UL);

  if (ti->tm_hour >= 8 && ti->tm_hour < 20) {
    uint32_t rst = preferences.getUInt(PDC_PREF_SCHED_MORN_RST, 0);
    uint32_t rbt = preferences.getUInt(PDC_PREF_SCHED_MORN_RBT, 0);
    if (rst == dayTag && rbt != dayTag && can_hard_fallback) {
      g_sched_fallback_restart_ms = mnow;
      pdcPrefsPutUInt(PDC_PREF_SCHED_RST_DAY, dayTag);
      pdcPrefsPutUInt(PDC_PREF_SCHED_RST_SLOT, 0);
      pdcPrefsPutUInt(PDC_PREF_SCHED_RST_PEND, 1);
      pdcPersistSessCountersNvs();
      delay(100);
      ESP.restart();
    }
  }
  if (ti->tm_hour >= 20) {
    uint32_t rst = preferences.getUInt(PDC_PREF_SCHED_EVE_RST, 0);
    uint32_t rbt = preferences.getUInt(PDC_PREF_SCHED_EVE_RBT, 0);
    if (rst == dayTag && rbt != dayTag && can_hard_fallback) {
      g_sched_fallback_restart_ms = mnow;
      pdcPrefsPutUInt(PDC_PREF_SCHED_RST_DAY, dayTag);
      pdcPrefsPutUInt(PDC_PREF_SCHED_RST_SLOT, 1);
      pdcPrefsPutUInt(PDC_PREF_SCHED_RST_PEND, 1);
      pdcPersistSessCountersNvs();
      delay(100);
      ESP.restart();
    }
  }
}

void updateLastShotTime() {

  if (!isTimeValid()) {
    Serial.println("Ignoring shot — time not synchronized yet");
    return;
  }
  time_t now = time(nullptr);
  lastShotEpoch = now;
  idle45Sent = false;

  struct tm *timeinfo = localtime(&now);
  char buffer[30];
  strftime(buffer, sizeof(buffer), "%Y-%m-%d %H:%M:%S", timeinfo);

  Serial.print("Last Shot Timestamp: ");
  Serial.println(buffer);
}


void whatsappTask(void *parameter) {
  Serial.println("WhatsApp task started");
  while (true) {
    if (whatsapp_req && !whatsapp_sent && WiFi.status() == WL_CONNECTED) {
      Serial.println("Background WhatsApp send started");
      WiFiClientSecure client;
      client.setInsecure();
      HTTPClient http;
      const char* url ="https://alubee-whatsapp-bot-841494023550.asia-south1.run.app/";
      if (http.begin(client, url)) {
        http.addHeader("Content-Type", "application/json");
        int code = http.POST(payload_req);
        Serial.print("WhatsApp HTTP code: ");
        Serial.println(code);
        if (code == HTTP_CODE_OK || code == HTTP_CODE_ACCEPTED) {
          whatsapp_sent = true; 
          Serial.println("WhatsApp sent successfully");
        }
        http.end();
      }
    }
    vTaskDelay(2000 / portTICK_PERIOD_MS);
  }
}



void send_data(String json_data) {
  if (bufferMutex != NULL && xSemaphoreTake(bufferMutex, (TickType_t)10) == pdTRUE) {
    payloadBuffer.push_back(json_data);
    Serial.println("Send Data Initiated...");
    xSemaphoreGive(bufferMutex);
  }
}


void httpSenderTask(void *parameter) {
  while (true) {
    if (WiFi.status() == WL_CONNECTED) {
      if (bufferMutex != NULL && xSemaphoreTake(bufferMutex, (TickType_t)10) == pdTRUE) {
        if (!payloadBuffer.empty()) {
          String jsonPayload = payloadBuffer.front();
          Serial.println(jsonPayload);
          payloadBuffer.erase(payloadBuffer.begin());  // remove from buffer
          xSemaphoreGive(bufferMutex);
          const char* serverUrl = "https://production-loader-841494023550.asia-south1.run.app";
          HTTPClient http;
          http.begin(serverUrl);
          http.addHeader("Content-Type", "application/json");
          int httpResponseCode = http.POST(jsonPayload);
          if (httpResponseCode > 0) {
            String response = http.getString();
            Serial.println("Response Code: " + String(httpResponseCode));
            Serial.println("Response Body: " + response);
            if (restartRequested && jsonPayload.indexOf("\"measurement\":33") >= 0 && (httpResponseCode == HTTP_CODE_OK || httpResponseCode == HTTP_CODE_ACCEPTED))
            {       
              Serial.println("SERVER ACK RECEIVED FOR SHIFT DATA");
              restartAckReceived = true;
            }
          } 
          else {
            Serial.println("POST Failed: " + http.errorToString(httpResponseCode));
            // Add back to buffer on failure
            if (bufferMutex != NULL && xSemaphoreTake(bufferMutex, (TickType_t)10) == pdTRUE) {
              payloadBuffer.insert(payloadBuffer.begin(), jsonPayload);  // Reinsert at front
              xSemaphoreGive(bufferMutex);
            }
            delay(5000); // Wait before retrying
          }

          http.end();
        } else {
          xSemaphoreGive(bufferMutex);
        }
      }
    }
    vTaskDelay(2000 / portTICK_PERIOD_MS);  // Run every 2 seconds
  }
}


void updatePayloadIdle(int state,int idleVal) {

  JsonDocument doc;
  DeserializationError err = deserializeJson(doc, payload_req);
  if (err) {
    Serial.println("Failed to parse payload_req");
    return;
  }

  if (state == 1) {
    time_t now = time(nullptr);
    struct tm *timeinfo = localtime(&now);
    char dt[25];
    strftime(dt, sizeof(dt), "%Y-%m-%d %H:%M:%S", timeinfo);
    req_datetime = String(dt);

    supervisor = doc.containsKey("Supervisor")
                   ? doc["Supervisor"].as<String>()
                   : "NA";

    preferences.putString("req_datetime", req_datetime);
    preferences.putString("supervisor", supervisor);

    doc["State"] = state;
    doc["IdleVal"]= idleVal;
    doc["Requested_Datetime"] = req_datetime;
    doc["Requested_Supervisor"] = supervisor;
  }
  else {

    req_datetime = preferences.getString("req_datetime", "NA");
    supervisor   = preferences.getString("supervisor", "NA");
    doc["State"] = state;
    doc["IdleVal"]= idleVal;
    doc["Requested_Datetime"] = req_datetime;
    doc["Requested_Supervisor"] = supervisor;
  }
  payload_req = "";
  serializeJson(doc, payload_req);
  Serial.println(payload_req);
}



void debounceButton(int pin, int &lastButtonState, int &buttonState, unsigned long &lastDebounceTime, bool &countFlag, int idleValue) {

  int reading = digitalRead(pin);

  if (reading != lastButtonState) {
    lastDebounceTime = millis();
  }

  if ((millis() - lastDebounceTime) > debounceDelay) {
    if (reading != buttonState) {
      buttonState = reading;

      if (buttonState == HIGH) {
        if (idle45Sent) {
          String payload = "{";
          payload += "\"device_id\":" + String(deviceID) + ",";
          payload += "\"measurement\":45,";
          payload += "\"value\":0,";
          payload += "\"partNo\":\"" + partNo + "\",";
          payload += "\"item_code\":\"" + itemCode + "\"";
          payload += "}";
          send_data(payload);
          idle45Sent = false;
          updateLastShotTime();             // optional but recommended
          Serial.println("IDLE 45 CLEARED (Production resumed via idle button)");
        }
        if (!countFlag) {
          idle = idleValue;
          countFlag = true;
          updatePayloadIdle(1,idleValue); 
          whatsapp_req = true;
          whatsapp_sent = false;
          Serial.println(payload_req);
          send_flag=false;
          preferences.putUInt("idle", idleValue);
          preferences.putUInt("count_flag", countFlag);
          if(idle!=0){
          String payload = "{";
          payload += "\"device_id\":" + String(deviceID) + ",";    
          payload += "\"measurement\":" + String(idle) + ","; 
          payload += "\"value\":1,";
          payload += "\"partNo\":\"" + partNo + "\",";
          payload += "\"item_code\":\"" + itemCode + "\"";
          payload += "}";
          send_data(payload);
          }
        } else {
          updateLastShotTime();
          updatePayloadIdle(0,idleValue);
          whatsapp_req = true;
          whatsapp_sent = false;
          preferences.putUInt("idle", 0);
          preferences.putUInt("count_flag", countFlag);
          if(idle!=0){
          send_flag=true;
          String payload = "{";
          payload += "\"device_id\":" + String(deviceID) + ",";    
          payload += "\"measurement\":" + String(idle) + ","; 
          payload += "\"value\":0,";
          payload += "\"partNo\":\"" + partNo + "\",";
          payload += "\"item_code\":\"" + itemCode + "\"";
          payload += "}";
          send_data(payload);
          if(idle==34){plan_req=true;}
          }
          idle = 0;
          countFlag = false;
        }
      }
    }
  }

  lastButtonState = reading;
}

void handleBreakButton() {
  debounceButton(16, lastBreakButtonState, breakButtonState, lastDebounceTimeBreak, count_flag, 16);
}

void handleSettingButton() {
  debounceButton(19, lastSettingButtonState, settingButtonState, lastDebounceTimeSetting, count_flag, 19);
}

void handleMaintenanceButton() {
  debounceButton(18, lastMaintenanceButtonState, maintenanceButtonState, lastDebounceTimeMaintenance, count_flag, 18);
}

void handleManPowerButton() {
  debounceButton(4, lastManPowerButtonState, ManPowerButtonState, lastDebounceTimeManPower, count_flag, 4);
}

void handleNoloadButton() {
  debounceButton(17, lastNoloadButtonState, noloadButtonState, lastDebounceTimeNoload, count_flag, 17);
}

void handlePowercutButton() {
  debounceButton(5, lastPowercutButtonState, powercutButtonState, lastDebounceTimePowercut, count_flag, 5);
}

void handleToolChangeButton() {
  debounceButton(34, lastToolChangeButtonState, ToolChangeButtonState, lastDebounceTimeToolChange, count_flag, 34);
}

WiFiNetwork findBestWiFi() {
    int numNetworks = WiFi.scanNetworks();
    WiFiNetwork bestWiFi = {"", -100}; 
    const String allowedSSIDs[] = {
        "ADC-PDC-01", "ADC-PDC-02", "ADC-PDC-03", "ADC-PDC-04", "ADC-PDC-05", "ADC-PDC-06",
        "Alubee.4G-U1", "CNC-VMC-01", "CNC-VMC-02", "CNC-VMC-03", "CNC-VMC-04", "CNC-VMC-05"
    };
    const int allowedCount = sizeof(allowedSSIDs) / sizeof(allowedSSIDs[0]);
    if (numNetworks == 0) {
        Serial.println("No WiFi networks found.");
    } else {
        Serial.println("Scanning WiFi networks...");
        Serial.println("----------------------------------------------------");
        Serial.println("No | SSID              | RSSI (dBm) | Security Type");
        Serial.println("----------------------------------------------------");

        for (int i = 0; i < numNetworks; i++) {
            int rssi = WiFi.RSSI(i);
            String ssid = WiFi.SSID(i);
            int encType = WiFi.encryptionType(i);

            // Check if SSID is in the allowed list
            bool isAllowed = false;
            for (int j = 0; j < allowedCount; j++) {
                if (ssid == allowedSSIDs[j]) {
                    isAllowed = true;
                    break;
                }
            }

            if (isAllowed) {
                Serial.printf("%2d | %-17s | %4d dBm  | %s\n", 
                    i + 1, ssid.c_str(), rssi, 
                    (encType == WIFI_AUTH_OPEN) ? "Open" : "Secured");

                // Select the strongest allowed network
                if (rssi > bestWiFi.rssi) {
                    bestWiFi.ssid = ssid;
                    bestWiFi.rssi = rssi;
                }
            }
        }
        Serial.println("----------------------------------------------------");
    }

    return bestWiFi;
}

String getWiFiPassword(const String& ssid) {
    if (ssid == "Alubee.4G-U1") {
        return "alubee123";  
    }
    return "AlubIoT24"; 
}

bool connectToWiFi(const String& ssid) {
    String password = getWiFiPassword(ssid);
    Serial.printf("Connecting to WiFi: %s (%d dBm)...\n", ssid.c_str(), WiFi.RSSI());

    WiFi.begin(ssid.c_str(), password.c_str());
    unsigned long startTime = millis();

    while (WiFi.status() != WL_CONNECTED) {
        delay(500);
        Serial.print(".");
        
        if (millis() - startTime > WIFI_CONNECT_TIMEOUT) {
            Serial.println("\nConnection timeout! WiFi turning off.");
            WiFi.disconnect();
            WiFi.mode(WIFI_OFF);
            return false;
        }
    }

    Serial.println("\nConnected to WiFi!");
    wifi_check=true;
    Serial.printf("IP Address: %s\n", WiFi.localIP().toString().c_str());
    return true;
}

void connect_to_wifi(){
    WiFi.mode(WIFI_STA);
    WiFiNetwork bestWiFi = findBestWiFi();
    if (bestWiFi.ssid != "") {
        connectToWiFi(bestWiFi.ssid);
    } else {
        Serial.println("No suitable WiFi found. Turning WiFi off.");
        WiFi.mode(WIFI_OFF);
    }
}


void wifiManagerTask(void *parameter) {
  while (true) {
    if (WiFi.status() != WL_CONNECTED) {
      Serial.println("WiFi disconnected. Trying to reconnect...");
      WiFi.mode(WIFI_STA);
      WiFiNetwork bestWiFi = findBestWiFi();
      if (bestWiFi.ssid != "") {
        connectToWiFi(bestWiFi.ssid);
      } else {
        Serial.println("No suitable WiFi found. Turning off WiFi.");
        WiFi.mode(WIFI_OFF);
        wifi_check = false;
      }
    }
    vTaskDelay(10000 / portTICK_PERIOD_MS);
  }
}

void fetchPlanData() {

  Serial.println("fetchPlanData() called");

  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("WiFi not connected");
    return;
  }

  WiFiClientSecure client;
  client.setInsecure();

  HTTPClient http;

  String url =
    "https://alubee-plan-function-dcxtqmfpjq-el.a.run.app/"
    "?device_id="+deviceID;

  Serial.println(url);

  if (!http.begin(client, url)) {
    Serial.println("http.begin failed");
    return;
  }

  http.setTimeout(8000);
  int httpCode = http.GET();

  Serial.print("HTTP code: ");
  Serial.println(httpCode);
  

  if (httpCode != HTTP_CODE_OK) {
    http.end();
    return;
  }

  payload_req = http.getString();
  http.end();
  Serial.println(payload_req);
  JsonDocument doc;
  DeserializationError err = deserializeJson(doc, payload_req);
  if (err) {
    return;
  }


  if (xSemaphoreTake(planMutex, portMAX_DELAY) == pdTRUE) {
    partNo = doc["Part_No"] | "N/A";
    itemCode=doc["Item_Code"] | "N/A";
    if (doc["Production_Plan"].is<int>()) {
      productionPlan = String(doc["Production_Plan"].as<int>());
    } else {
      productionPlan = "N/A";
    }
    plan_req = false;
    Serial.println("Plan updated:");
    Serial.println(partNo);
    Serial.println(productionPlan);
    Serial.println(itemCode);

    xSemaphoreGive(planMutex);
  }
}


void planFetcherTask(void *parameter) {
  Serial.println("PlanFetcherTask started");
  vTaskDelay(10000 / portTICK_PERIOD_MS);  // allow WiFi to stabilize
  while (true) {
    if (plan_req && WiFi.status() == WL_CONNECTED) {
      Serial.println("plan_req = true → fetching plan");
      fetchPlanData();
    } else {
    }

    vTaskDelay(30000 / portTICK_PERIOD_MS);  // check every 30 sec
  }
}

String epochToDateTimeString(time_t epoch) {
  struct tm *timeinfo = localtime(&epoch);
  char buffer[25];
  strftime(buffer, sizeof(buffer), "%Y-%m-%d %H:%M:%S", timeinfo);
  return String(buffer);
}

static const char* idleMeasurementLabel(int code) {
  switch (code) {
    case 0: return "none (production)";
    case 4: return "man_power (measurement 4)";
    case 5: return "powercut (measurement 5)";
    case 16: return "break (measurement 16)";
    case 17: return "noload (measurement 17)";
    case 18: return "maintenance (measurement 18)";
    case 19: return "setting (measurement 19)";
    case 34: return "tool_change_mould (measurement 34)";
    case 45: return "idle_no_production (measurement 45)";
    default: return "unknown_idle_code";
  }
}

static const char* machineStatusSummary() {
  if (idle == 0) {
    if (idle45Sent) return "idle_no_production_signal";
    return "running";
  }
  switch (idle) {
    case 16: return "break_stoppage";
    case 19: return "setting_stoppage";
    case 18: return "maintenance_stoppage";
    case 4: return "manpower_stoppage";
    case 17: return "noload_stoppage";
    case 5: return "powercut_stoppage";
    case 34: return "mould_change_stoppage";
    default: return "stoppage_other";
  }
}

static bool isI2cDevicePresent(uint8_t address) {
  Wire.beginTransmission(address);
  return (Wire.endTransmission() == 0);
}

static const char* espResetReasonTag(esp_reset_reason_t r) {
  switch (r) {
    case ESP_RST_UNKNOWN: return "UNKNOWN";
    case ESP_RST_POWERON: return "POWERON";
    case ESP_RST_EXT: return "EXT";
    case ESP_RST_SW: return "SW_RESET";
    case ESP_RST_PANIC: return "PANIC";
    case ESP_RST_INT_WDT: return "INT_WDT";
    case ESP_RST_TASK_WDT: return "TASK_WDT";
    case ESP_RST_WDT: return "WDT_RESET";
    case ESP_RST_DEEPSLEEP: return "DEEPSLEEP";
    case ESP_RST_BROWNOUT: return "BROWNOUT";
    case ESP_RST_SDIO: return "SDIO";
    default: return "OTHER";
  }
}

/** Call only when registering a confirmed shot and `!restartRequested` (mirrors PDC shot path). */
static void vmcApplyShotCycleTelemetry(unsigned long currentMillis) {
  if (g_last_shot_millis != 0) {
    g_last_cycle_duration_ms = (uint32_t)(currentMillis - g_last_shot_millis);
    if (g_cycle_time_ms_ewma == 0)
      g_cycle_time_ms_ewma = g_last_cycle_duration_ms;
    else
      g_cycle_time_ms_ewma = (g_cycle_time_ms_ewma * 7 + g_last_cycle_duration_ms) / 8;
    const uint32_t thr = g_cycle_time_ms_ewma + (g_cycle_time_ms_ewma / 2) + 1000;
    g_abnormal_cycle = (g_last_cycle_duration_ms > thr && g_cycle_time_ms_ewma > 5000);
  } else {
    g_abnormal_cycle = false;
  }
  g_last_shot_millis = currentMillis;
}

void healthPayloadQueueTask(void* parameter) {
  Serial.println(F("Health payload queue task started (VMC TYPE I)"));
  vTaskDelay(pdMS_TO_TICKS(35000));
  for (;;) {
    esp_reset_reason_t rr = esp_reset_reason();
    int adc32 = analogRead(32);
    float v32 = (adc32 * 3.3f) / 4095.0f;
    const float chipTempC = temperatureRead();
    pinMode(32, INPUT_PULLDOWN);

    String payload = "{";
    payload += "\"device_id\":" + String(deviceID) + ",";
    payload += "\"measurement\":46,";
    payload += "\"value\":1,";
    payload += "\"partNo\":\"" + partNo + "\",";
    payload += "\"item_code\":\"" + itemCode + "\",";
    payload += "\"vmc_type\":\"TYPE_I\",";
    payload += "\"vmc_shot_detection\":\"ANALOG_1P5V_THEN_LOW_SHAPE\",";
    payload += "\"uptime_ms\":" + String((unsigned long)millis()) + ",";
    payload += "\"boot_count\":0,";
    {
      uint8_t mr = 0, mrt = 0, er = 0, ert = 0;
      pdcScheduledResetSlotsForTelemetry(&mr, &mrt, &er, &ert);
      payload += "\"scheduled_reset_morning_ok\":" + String((int)mr) + ",";
      payload += "\"scheduled_restart_morning_ok\":" + String((int)mrt) + ",";
      payload += "\"scheduled_reset_evening_ok\":" + String((int)er) + ",";
      payload += "\"scheduled_restart_evening_ok\":" + String((int)ert) + ",";
    }
    payload += "\"reset_reason\":\"" + String(espResetReasonTag(rr)) + "\",";
    payload += "\"wifi_status\":" + String((int)WiFi.status()) + ",";
    payload += "\"wifi_rssi_dbm\":" + String(WiFi.RSSI()) + ",";
    payload += "\"wifi_ip\":\"" + WiFi.localIP().toString() + "\",";
    payload += "\"wifi_mac\":\"" + WiFi.macAddress() + "\",";
    payload += "\"shot_count\":" + String(shot_count) + ",";
    payload += "\"idle_measurement_code\":" + String(idle) + ",";
    payload += "\"idle_measurement_label\":\"" + String(idleMeasurementLabel(idle)) + "\",";
    payload += "\"machine_status\":\"" + String(machineStatusSummary()) + "\",";
    payload += "\"free_heap_bytes\":" + String((unsigned)ESP.getFreeHeap()) + ",";
    payload += "\"min_free_heap_bytes\":" + String((unsigned)ESP.getMinFreeHeap()) + ",";
    payload += "\"loop_time_ms_avg\":" + String(g_loop_time_us_avg / 1000.0f, 2) + ",";
    payload += "\"loop_time_ms_max\":" + String(g_loop_time_us_max / 1000.0f, 2) + ",";
    payload += "\"error_count_today\":0,";
    payload += "\"cycle_time_ms_ewma\":" + String((unsigned long)g_cycle_time_ms_ewma) + ",";
    payload += "\"last_cycle_duration_ms\":" + String((unsigned long)g_last_cycle_duration_ms) + ",";
    payload += "\"abnormal_cycle_detected\":" + String(g_abnormal_cycle ? "true" : "false") + ",";
    payload += "\"last_shot_epoch\":" + String((long long)lastShotEpoch) + ",";
    payload += "\"last_watchdog_feed_ms_proxy\":" + String((unsigned long)g_last_loop_end_ms) + ",";
    payload += "\"gpio32_adc_raw\":" + String(adc32) + ",";
    payload += "\"gpio32_voltage_v\":" + String(v32, 3) + ",";
    payload += "\"gpio32_shot_signal_v\":" + String(v32, 3) + ",";
    if (!isnan(chipTempC) && chipTempC >= -40.0f && chipTempC <= 125.0f)
      payload += "\"chip_temp_c\":" + String(chipTempC, 1) + ",";
    else
      payload += "\"chip_temp_c\":null,";
    payload += "\"wifi_disconnect_count\":0,";
    payload += "\"wifi_reconnect_count\":0,";
    payload += "\"i2c_lcd_0x27_present\":" + String(g_i2c_lcd_present ? "true" : "false") + ",";
    payload += "\"i2c_lcd_probe_fail_count\":" + String((uint32_t)g_i2c_lcd_probe_fail_count) + ",";
    payload += "\"i2c_garbage_suspected\":" + String(g_i2c_lcd_present ? "false" : "true");
    payload += "}";

    send_data(payload);
    vTaskDelay(pdMS_TO_TICKS(VMC_HEALTH_PUBSUB_PUSH_INTERVAL_MS));
  }
}


void setup() {
  Serial.begin(115200);
  pinMode(32, INPUT_PULLDOWN);
  pinMode(36, INPUT_PULLDOWN);
  pinMode(16, INPUT_PULLDOWN);
  pinMode(19, INPUT_PULLDOWN);
  pinMode(18, INPUT_PULLDOWN);
  pinMode(4, INPUT_PULLDOWN);
  pinMode(17, INPUT_PULLDOWN);
  pinMode(5, INPUT_PULLDOWN);
  pinMode(34, INPUT_PULLDOWN);
  pinMode(33, OUTPUT);
  pinMode(23, OUTPUT);
  digitalWrite(33,LOW);
  digitalWrite(23,LOW);
  Wire.begin(21, 22);  
  lcd.begin(16, 2);
  lcd.setBacklight(255); 
  preferences.begin("my-app", false);
  pdcMigrateLegacySchedNvs();
  pdcAckScheduledRestartFromNvs();
  pdcApplyBootSessionCountersFromNvs();
  deviceID=preferences.getString("deviceID", "Unknown");
  idle = preferences.getUInt("idle", 0);
  count_flag = preferences.getUInt("count_flag", false);
  restart_flag = preferences.getUInt("restart_flag", false);
  shot_count = preferences.getUInt("shot_count", 0);
  partNo=preferences.getString("partNo", "N/A");
  productionPlan=preferences.getString("productionPlan", "N/A");
  configTime(gmtOffset_sec, daylightOffset_sec, ntpServer);
  xTaskCreatePinnedToCore(wifiManagerTask, "WiFiManager", 4096, NULL, 1, NULL, 1);
  bufferMutex = xSemaphoreCreateMutex();
  planMutex = xSemaphoreCreateMutex();
  xTaskCreatePinnedToCore(httpSenderTask, "HttpSender", 8192, NULL, 1, NULL, 0);

  if (planMutex == NULL) {
  Serial.println("planMutex creation failed");
  }
  BaseType_t result =xTaskCreatePinnedToCore(planFetcherTask,"PlanFetcher",8192,NULL,1,NULL,0);
  if (result == pdPASS) {
    Serial.println("PlanFetcher task created");
  } else {
    Serial.println("PlanFetcher task creation failed");
  }
  xTaskCreatePinnedToCore(whatsappTask,"WhatsAppTask",8192,NULL,1,NULL,0);
  xTaskCreatePinnedToCore(healthPayloadQueueTask, "HealthQueue", VMC_HEALTH_QUEUE_TASK_STACK, NULL, 1, NULL, 0);

  time_t now = time(nullptr);
  struct tm *timeinfo = localtime(&now);
  char dt[25];
  strftime(dt, sizeof(dt), "%Y-%m-%d %H:%M:%S", timeinfo);
  req_datetime = String(dt);

}

void loop() {

  {
    static uint32_t prev_loop_us = 0;
    const uint32_t now_us = micros();
    if (prev_loop_us != 0) {
      uint32_t dt = now_us - prev_loop_us;
      if (dt > g_loop_time_us_max)
        g_loop_time_us_max = dt;
      g_loop_time_us_avg = (g_loop_time_us_avg == 0) ? dt : (g_loop_time_us_avg * 15 + dt) / 16;
    }
    prev_loop_us = now_us;
  }

  if (millis() - g_last_i2c_probe_ms >= 10000UL) {
    g_last_i2c_probe_ms = millis();
    bool present = isI2cDevicePresent(0x27);
    g_i2c_lcd_present = present;
    if (!present)
      g_i2c_lcd_probe_fail_count++;
  }

  if(isTimeValid()){
  if(idle==16){handleBreakButton();}
  else if(idle==19){handleSettingButton();}
  else if(idle==18){handleMaintenanceButton();}
  else if(idle==4){handleManPowerButton();}
  else if(idle==17){handleNoloadButton();}
  else if(idle==5){handlePowercutButton();}
  else if(idle==34){handleToolChangeButton();}
  else{
  handleBreakButton();
  handleSettingButton();
  handleMaintenanceButton();
  handleManPowerButton();
  handleNoloadButton();
  handlePowercutButton();
  handleToolChangeButton();
  }
  }
  time_t now = time(nullptr);
  struct tm *timeinfo = localtime(&now);
  char dateStr[9];
  strftime(dateStr, sizeof(dateStr), "%H:%M", timeinfo); 


  int analogValue = analogRead(32); // Read the analog value from pin 32
  float voltage = (analogValue * 3.3) / 4095.0;
  
  if (voltage>1.5) {
    stop_time = 0;
    if (high_count == 0) {
      start_time = millis();
    }
    if (high_count >= 50) { high_count = 0; }
    high_count++;
    low_count = 0;
  } else {
    if (low_count == 0) {
      stop_time = millis();
    }
    if (low_count >= 50) { low_count = 0; }
    low_count++;
    high_count = 0;
  }

  if (high_count > 15 && low_count == 0 && millis() - start_time >= 3000 && !high_flag) {
    Serial.println("Pin is High for Three seconds");
    high_count = 0;
    high_flag = true;
  } else if (high_count == 0 && low_count > 4 && millis() - stop_time >= 3000 && high_flag) {
    Serial.println("Pin is Low for Three seconds");
    if (!restartRequested) {
      if (idle45Sent) {
        String payload = "{";
        payload += "\"device_id\":" + String(deviceID) + ",";
        payload += "\"measurement\":45,";
        payload += "\"value\":0,";
        payload += "\"partNo\":\"" + partNo + "\",";
        payload += "\"item_code\":\"" + itemCode + "\"";
        payload += "}";
        send_data(payload);
        idle45Sent = false;
        Serial.println("IDLE 45 CLEARED (Production resumed)");
      }
      low_count = 0;
      unsigned long shotMs = millis();
      vmcApplyShotCycleTelemetry(shotMs);
      shot_count++;
      updateLastShotTime();
      preferences.putUInt("shot_count", shot_count);
      String payload = "{";
      payload += "\"device_id\":" + String(deviceID) + ",";
      payload += "\"measurement\":" + String(32) + ",";
      payload += "\"value\":" + String(shot_count) + ",";
      payload += "\"partNo\":\"" + partNo + "\",";
      payload += "\"item_code\":\"" + itemCode + "\"";
      payload += "}";
      if (shot_count % 5 == 0) {
        send_data(payload);
      }
      high_flag = false;
    } else {
      low_count = 0;
      high_flag = false;
    }
  }


  if(WiFi.status() != WL_CONNECTED && wifi_check){
    WiFi.mode(WIFI_OFF);
    wifi_check=false; 
   }
   
  int currentHour = timeinfo->tm_hour;
  int currentMinute = timeinfo->tm_min;
  int currentSecond = timeinfo->tm_sec;
    
  if (millis() - lastLcdUpdate >= lcdUpdateInterval) {
      lastLcdUpdate = millis();
      lcd.clear();
      lcd.setCursor(0, 0);
  
      if (idle == 16) {
          lcd.print("Break");
          digitalWrite(33, LOW);
          digitalWrite(23, HIGH);
      } else if (idle == 19) {
          lcd.print("Setting");
          digitalWrite(33, LOW);
          digitalWrite(23, HIGH);
      } else if (idle == 18) {
          lcd.print("Maintain");
          digitalWrite(33, LOW);
          digitalWrite(23, HIGH);
      } else if (idle == 4) {
          lcd.print("Man Power");
          digitalWrite(33, LOW);
          digitalWrite(23, HIGH);
      } else if (idle == 17) {
          lcd.print("Noload");
          digitalWrite(33, LOW);
          digitalWrite(23, HIGH);
      } else if (idle == 5) {
          lcd.print("Powercut");
          digitalWrite(33, LOW);
          digitalWrite(23, HIGH);
      } 
      else if (idle == 34) {
          lcd.print("Tool");
          digitalWrite(33, LOW);
          digitalWrite(23, HIGH);
      }
      else {
          if (partNo == "" || partNo == "null") {
              lcd.print("N/A");
          } else {
              lcd.print(partNo.length() > 10 ? partNo.substring(0, 10) : partNo);
          }
          digitalWrite(33, HIGH);
          digitalWrite(23, LOW);
      }
      delay(50);
      lcd.setCursor(11, 0);
        if (showRSSI) {
          lcd.print(WiFi.RSSI());
      } else {
          lcd.print(dateStr);
      }
      showRSSI = !showRSSI;  
      lcd.setCursor(0, 1);
      lcd.print("S:");
      lcd.print(shot_count);
      lcd.setCursor(10, 1);
      lcd.print("P:");
      if (productionPlan.isEmpty()) {
          lcd.print("N/A");
      } else {
          lcd.print(productionPlan);
      }
  }

  time_t nowEpoch = time(nullptr);

  if (idle == 0 && lastShotEpoch > 0 && !idle45Sent) {
    long diffSeconds = nowEpoch - lastShotEpoch;
    if (diffSeconds < 0) return;
    if (diffSeconds >= 600) {  
      JsonDocument doc;
      DeserializationError err = deserializeJson(doc, payload_req);
      if (err) {
      Serial.println("Failed to parse payload_req");
        return;
      }
      doc["State"] = 1;
      doc["IdleVal"]= 45;
      doc["Requested_Datetime"] = epochToDateTimeString(lastShotEpoch);
      doc["Requested_Supervisor"] = supervisor;
      payload_req = "";
      serializeJson(doc, payload_req);
      Serial.println(payload_req);
      whatsapp_req = true;
      whatsapp_sent = false;
      String payload = "{";
      payload += "\"device_id\":" + String(deviceID) + ",";
      payload += "\"measurement\":45,";
      payload += "\"value\":1,";
      payload += "\"partNo\":\"" + partNo + "\",";
      payload += "\"item_code\":\"" + itemCode + "\"";
      payload += "}";
      idle45Sent = true; 
      Serial.println("IDLE 45 TRIGGERED (No production)");
      send_data(payload);
    }
    }
 
  if (currentSecond > 5) {
    resetDone = false;
    last_idle_sent=true;
  }

  if (((currentHour == 19 || currentHour == 7) && (currentMinute == 59) && currentSecond <3 && idle==0 && last_idle_sent && idle45Sent)){
      String payload = "{";
      payload += "\"device_id\":" + String(deviceID) + ",";
      payload += "\"measurement\":45,";
      payload += "\"value\":0,";
      payload += "\"partNo\":\"" + partNo + "\",";
      payload += "\"item_code\":\"" + itemCode + "\"";
      payload += "}";
      send_data(payload);
      last_idle_sent=false;
      
  }
  else if (((currentHour == 20 || currentHour == 8) && (currentMinute == 1) && currentSecond <3 && idle==0 && !idle45Sent && last_idle_sent)){
      updateLastShotTime();
      last_idle_sent=false;
  }

  else if (((currentHour == 19 || currentHour == 7) && (currentMinute == 59) && currentSecond <3 && idle!=0 && last_idle_sent)) {
  
          String payload = "{";
          payload += "\"device_id\":" + String(deviceID) + ",";    
          payload += "\"measurement\":" + String(idle) + ","; 
          payload += "\"value\":0,";
          payload += "\"partNo\":\"" + partNo + "\",";
          payload += "\"item_code\":\"" + itemCode + "\"";
          payload += "}";
          send_data(payload);
          last_idle_sent=false;
    }
   else if(((currentHour == 20 || currentHour == 8) && (currentMinute == 1) && currentSecond <3 && idle!=0 && last_idle_sent)){
  
          String payload = "{";
          payload += "\"device_id\":" + String(deviceID) + ",";    
          payload += "\"measurement\":" + String(idle) + ","; 
          payload += "\"value\":1,";
          payload += "\"partNo\":\"" + partNo + "\",";
          payload += "\"item_code\":\"" + itemCode + "\"";
          payload += "}";
          send_data(payload);
          last_idle_sent=false;
    }

  
  /* Scheduled business reset: 08:00 and 20:00 — same NVS + fire_id pattern as TEST_PDC (enables meas 46 flags). */
  if (isTimeValid() && timeinfo) {
    const bool slot_morn_prod = (currentHour == 8 && currentMinute ==0 && currentSecond < 12);
    const bool slot_eve_prod = (currentHour == 20 && currentMinute == 0 && currentSecond < 12);
    uint32_t dtag = pdcLocalCalendarTag(timeinfo);
    uint64_t fire_id = 0;
    if (slot_morn_prod || slot_eve_prod)
      fire_id = (uint64_t)dtag * 10000ull + (uint64_t)(currentHour * 100 + currentMinute);

    if (fire_id != 0 && fire_id != g_schedrst_last_fire_id) {
      /* NVS RST survives ESP.restart(); RAM fire_id dedup does not — skip 2nd meas 33 in same :00 window. */
      const bool already_rst_today =
          (slot_morn_prod && preferences.getUInt(PDC_PREF_SCHED_MORN_RST, 0) == dtag) ||
          (slot_eve_prod && preferences.getUInt(PDC_PREF_SCHED_EVE_RST, 0) == dtag);
      if (already_rst_today) {
        g_schedrst_last_fire_id = fire_id;
      } else {
      g_schedrst_last_fire_id = fire_id;
      resetDone = true;
      lcd.clear();
      lcd.setCursor(0, 0);
      lcd.print("Resetting...");
      delay(1000);
      send_flag = true;
      String payload = "{";
      payload += "\"device_id\":" + String(deviceID) + ",";
      payload += "\"measurement\":" + String(33) + ",";
      payload += "\"value\":" + String(shot_count) + ",";
      payload += "\"partNo\":\"" + partNo + "\",";
      payload += "\"item_code\":\"" + itemCode + "\"";
      payload += "}";
      send_data(payload);
      pdcPrefsPutUInt("shot_count", 0);
      shot_count = 0;
      g_last_shot_millis = 0;
      g_last_cycle_duration_ms = 0;
      g_cycle_time_ms_ewma = 0;
      g_abnormal_cycle = false;
      partNo = "N/A";
      productionPlan = "N/A";
      plan_req = true;
      delay(500);
      Serial.println("Reset complete, restarting ESP...");
      {
        uint32_t calTag = pdcLocalCalendarTag(timeinfo);
        const bool morning_slot = slot_morn_prod;
        if (morning_slot) {
          pdcPrefsPutUInt(PDC_PREF_SCHED_MORN_RST, calTag);
          g_scheduled_safe_restart_slot = 0;
        } else {
          pdcPrefsPutUInt(PDC_PREF_SCHED_EVE_RST, calTag);
          g_scheduled_safe_restart_slot = 1;
        }
        g_sched_rst_write_ms = millis();
      }
      restartAckReceived = false;
      restartRequested = true;
      }
    }
  }

  // -------- SAFE RESTART CONTROLLER (same as TEST_PDC) --------
  if (restartRequested && restartAckReceived && !g_safe_restart_in_progress) {
    g_safe_restart_in_progress = true;
    restartAckReceived = false;
    Serial.println("Data confirmed. Performing safe restart.");
    lcd.clear();
    lcd.setCursor(0, 0);
    lcd.print("Restarting...");
    delay(2000);
    restart_flag = true;
    pdcPrefsPutUInt("shot_count", 0);
    pdcPrefsPutUInt("idle", idle);
    pdcPrefsPutUInt("count_flag", count_flag);
    pdcPrefsPutUInt("restart_flag", restart_flag);
    g_last_shot_millis = 0;
    g_last_cycle_duration_ms = 0;
    g_cycle_time_ms_ewma = 0;
    g_abnormal_cycle = false;
    if (isTimeValid()) {
      pdcPrefsPutULong64("wall_epoch_at_last_shutdown", (uint64_t)time(nullptr));
      time_t n = time(nullptr);
      struct tm* tsched = localtime(&n);
      if (tsched) {
        uint32_t tag = pdcLocalCalendarTag(tsched);
        pdcPrefsPutUInt(PDC_PREF_SCHED_RST_DAY, tag);
        pdcPrefsPutUInt(PDC_PREF_SCHED_RST_SLOT, (uint32_t)g_scheduled_safe_restart_slot);
        pdcPrefsPutUInt(PDC_PREF_SCHED_RST_PEND, 1);
      }
    }
    pdcPersistSessCountersNvs();
    restartRequested = false;
    ESP.restart();
  }

  pdcMaybeScheduledRestart();

  g_last_loop_end_ms = millis();
}

void saveCounter() {
  preferences.putUInt("shot_count", shot_count);
  preferences.putUInt("idle", idle);
  preferences.putUInt("count_flag", count_flag);
  preferences.putString("Requested_Datetime", req_datetime);
  preferences.putUInt("restart_flag", restart_flag);
  preferences.putString("Requested_Supervisor", supervisor);
}

void onPowerLoss() {
  saveCounter();
}

void onRestart() {
  saveCounter();
}
