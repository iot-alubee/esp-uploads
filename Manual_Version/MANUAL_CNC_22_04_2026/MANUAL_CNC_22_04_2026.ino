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

bool resetDone=false;

unsigned long previousMillis = 0;
const unsigned long interval = 20000;

String partNo;
String itemCode;
String productionPlan;
SemaphoreHandle_t planMutex;


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

  time_t now = time(nullptr);
  struct tm *timeinfo = localtime(&now);
  char dt[25];
  strftime(dt, sizeof(dt), "%Y-%m-%d %H:%M:%S", timeinfo);
  req_datetime = String(dt);

}

void loop() {

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

  int analogValue = analogRead(32);
  float voltage = (analogValue * 3.3) / 4095.0;
  unsigned long currentMillis = millis();

  if (voltage > 3.2) {
    if (currentMillis - previousMillis >= interval) {
      previousMillis = currentMillis;
      if (idle45Sent) {
        String payload = "{";
        payload += "\"device_id\":" + String(deviceID) + ",";
        payload += "\"measurement\":45,";
        payload += "\"value\":0,";
        payload += "\"partNo\":\"" + partNo + "\",";
        payload += "\"item_code\":\"" + itemCode + "\"";
        payload += "}";
        send_data(payload);
        idle45Sent=false;
        Serial.println("IDLE 45 CLEARED (Production resumed)");
      }
      updateLastShotTime();
      send_flag=true;
      shot_count = shot_count + 1;
      preferences.putUInt("shot_count", shot_count);
      if(shot_count%5==0){
        String payload = "{";
        payload += "\"device_id\":" + String(deviceID) + ",";               
        payload += "\"measurement\":" + String(32) + ",";             
        payload += "\"value\":" + String(shot_count)+ ",";
        payload += "\"partNo\":\"" + partNo + "\",";
        payload += "\"item_code\":\"" + itemCode + "\"";
        payload += "}";
        send_data(payload);
      }
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
    if (diffSeconds >= 300 && !idle45Sent) {  
      JsonDocument doc;
      DeserializationError err = deserializeJson(doc, payload_req);
      if (err) {
      Serial.println("Failed to parse payload_req");
        return;
      }
      idle45Sent = true; 
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
  else if (((currentHour == 20 || currentHour == 8) && (currentMinute == 1) && currentSecond <3 && idle==0 && last_idle_sent)){
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

  
  if (((currentHour == 20 || currentHour == 8) && (currentMinute == 0) && currentSecond <= 3 && !resetDone)) {
    resetDone = true;  
    lcd.clear();
    lcd.setCursor(0, 0);
    lcd.print("Resetting...");
    delay(1000);
    send_flag=true;
    String payload = "{";
    payload += "\"device_id\":" + String(deviceID) + ",";               
    payload += "\"measurement\":" + String(33) + ",";               
    payload += "\"value\":" + String(shot_count)+ ",";
    payload += "\"partNo\":\"" + partNo + "\",";
    payload += "\"item_code\":\"" + itemCode + "\"";
    payload += "}";
    send_data(payload);
    preferences.putUInt("shot_count", 0);
    shot_count = 0;
    partNo = "N/A";
    productionPlan = "N/A";
    plan_req=true;
    delay(500);
    Serial.println("Reset complete, restarting ESP...");
    restartRequested = true;
  }

  // -------- SAFE RESTART CONTROLLER --------
  if (restartRequested && restartAckReceived) {
    Serial.println("Data confirmed. Performing safe restart.");
    lcd.clear();
    lcd.setCursor(0,0);
    lcd.print("Restarting...");
    delay(2000);
    restart_flag=true;
    preferences.putUInt("shot_count", 0);
    preferences.putUInt("idle", idle);
    preferences.putUInt("count_flag", count_flag);
    preferences.putUInt("restart_flag", restart_flag);
    ESP.restart();
  }
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
