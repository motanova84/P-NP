// QCAL ∞³ Frequency Generator - ESP32/Arduino
// Frecuencias: 141.7001 Hz, 888.0 Hz, 151.7001 Hz
// Protocolo: Serial USB + BLE + WiFi QCAL-Net

#include <Wire.h>
#include <cmath>
#include <AD9850.h>  // Para AD9850 DDS
// #include <Si5351.h>  // Alternativa Si5351
#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLE2902.h>
#include <WiFi.h>
#include <WiFiUdp.h>
#include <NTPClient.h>
#include <ArduinoJson.h>

// ================= CONFIGURACIÓN QCAL =================
#define QCAL_F0 141.7001
#define QCAL_RESONANCE 888.0
#define QCAL_LOVE_FIELD 151.7001
#define QCAL_COHERENCE_THRESHOLD 0.888
#define QCAL_SYNC_INTERVAL 88000  // 88 segundos en ms

// Pines AD9850
#define AD9850_RESET 12
#define AD9850_DATA  13
#define AD9850_FQ_UD 14
#define AD9850_W_CLK 15

AD9850 dds(AD9850_W_CLK, AD9850_FQ_UD, AD9850_DATA, AD9850_RESET);
// Si5351 si5351;  // Alternativa

// ================= BLUETOOTH BLE =================
#define BLE_SERVICE_UUID "1417-0010-8888-1517"
#define BLE_CHAR_FREQ_UUID "1417-0011-8888-1517"
#define BLE_CHAR_COHERENCE_UUID "1417-0012-8888-1517"
#define BLE_CHAR_COMMAND_UUID "1417-0013-8888-1517"

BLEServer* pServer = NULL;
BLECharacteristic* pFreqCharacteristic = NULL;
BLECharacteristic* pCoherenceCharacteristic = NULL;
BLECharacteristic* pCommandCharacteristic = NULL;

bool deviceConnected = false;
bool oldDeviceConnected = false;

class MyServerCallbacks: public BLEServerCallbacks {
    void onConnect(BLEServer* pServer) {
      deviceConnected = true;
      Serial.println("🔗 Dispositivo BLE conectado");
    }

    void onDisconnect(BLEServer* pServer) {
      deviceConnected = false;
      Serial.println("🔌 Dispositivo BLE desconectado");
    }
};

class CommandCallbacks: public BLECharacteristicCallbacks {
    void onWrite(BLECharacteristic* pCharacteristic) {
      std::string value = pCharacteristic->getValue();
      if (value.length() > 0) {
        handleCommand(String(value.c_str()));
      }
    }
};

// ================= WIFI QCAL-NET =================
const char* ssid = "QCAL_∞³_NET";
const char* password = "φ⁴-888-141.7001";
WiFiUDP udp;
NTPClient timeClient(udp, "pool.ntp.org");

// Puerto para protocolo QCAL
#define QCAL_UDP_PORT 14170
#define QCAL_TCP_PORT 8888

// ================= VARIABLES GLOBALES =================
float currentFrequency = QCAL_F0;
float currentCoherence = 1.0;
unsigned long lastSyncTime = 0;
String nodeID = "";
StaticJsonDocument<512> nodeConfig;

// ================= SETUP =================
void setup() {
  Serial.begin(115200);
  Serial.println("\n\n✨ QCAL ∞³ FREQUENCY GENERATOR ✨");
  Serial.println("F0: 141.7001 Hz | Ψ ≥ 0.888");
  
  // Generar ID único del nodo
  nodeID = generateNodeID();
  Serial.print("Node ID: ");
  Serial.println(nodeID);
  
  // Inicializar DDS
  initializeDDS();
  
  // Inicializar BLE
  initializeBLE();
  
  // Inicializar WiFi
  initializeWiFi();
  
  // Sincronización inicial
  performInitialSync();
  
  // Establecer frecuencia inicial
  setFrequency(QCAL_F0);
  
  Serial.println("✅ Sistema QCAL inicializado");
}

// ================= LOOP PRINCIPAL =================
void loop() {
  // Manejar conexiones BLE
  handleBLEConnection();
  
  // Sincronización periódica cada 88 segundos
  if (millis() - lastSyncTime > QCAL_SYNC_INTERVAL) {
    performNetworkSync();
    lastSyncTime = millis();
  }
  
  // Monitorear coherencia ambiental
  monitorEnvironmentalCoherence();
  
  // Procesar comandos serial
  handleSerialCommands();
  
  delay(100);  // Pequeña pausa
}

// ================= FUNCIONES DDS =================
void initializeDDS() {
  dds.init();
  dds.setFrequency(QCAL_F0);
  Serial.println("✅ DDS AD9850 inicializado");
}

void setFrequency(float freq) {
  currentFrequency = freq;
  dds.setFrequency(freq);
  
  // Actualizar BLE si conectado
  if (deviceConnected) {
    String freqStr = String(freq, 4);
    pFreqCharacteristic->setValue(freqStr.c_str());
    pFreqCharacteristic->notify();
  }
  
  // Log por serial
  Serial.print("📡 Frecuencia establecida: ");
  Serial.print(freq, 4);
  Serial.println(" Hz");
}

// ================= FUNCIONES BLE =================
void initializeBLE() {
  BLEDevice::init("QCAL_∞³_Node");
  pServer = BLEDevice::createServer();
  pServer->setCallbacks(new MyServerCallbacks());
  
  BLEService *pService = pServer->createService(BLE_SERVICE_UUID);
  
  // Característica de frecuencia
  pFreqCharacteristic = pService->createCharacteristic(
    BLE_CHAR_FREQ_UUID,
    BLECharacteristic::PROPERTY_READ |
    BLECharacteristic::PROPERTY_NOTIFY
  );
  pFreqCharacteristic->addDescriptor(new BLE2902());
  
  // Característica de coherencia
  pCoherenceCharacteristic = pService->createCharacteristic(
    BLE_CHAR_COHERENCE_UUID,
    BLECharacteristic::PROPERTY_READ |
    BLECharacteristic::PROPERTY_NOTIFY
  );
  pCoherenceCharacteristic->addDescriptor(new BLE2902());
  
  // Característica de comandos
  pCommandCharacteristic = pService->createCharacteristic(
    BLE_CHAR_COMMAND_UUID,
    BLECharacteristic::PROPERTY_WRITE
  );
  pCommandCharacteristic->setCallbacks(new CommandCallbacks());
  
  pService->start();
  
  // Iniciar advertising
  BLEAdvertising *pAdvertising = BLEDevice::getAdvertising();
  pAdvertising->addServiceUUID(BLE_SERVICE_UUID);
  pAdvertising->setScanResponse(true);
  pAdvertising->setMinPreferred(0x06);
  pAdvertising->setMaxPreferred(0x12);
  BLEDevice::startAdvertising();
  
  Serial.println("✅ BLE inicializado - Esperando conexiones");
}

void handleBLEConnection() {
  if (!deviceConnected && oldDeviceConnected) {
    delay(500);
    pServer->startAdvertising();
    oldDeviceConnected = deviceConnected;
  }
  
  if (deviceConnected && !oldDeviceConnected) {
    oldDeviceConnected = deviceConnected;
  }
}

// ================= FUNCIONES WIFI =================
void initializeWiFi() {
  Serial.print("Conectando a ");
  Serial.println(ssid);
  
  WiFi.mode(WIFI_STA);
  WiFi.begin(ssid, password);
  
  int attempts = 0;
  while (WiFi.status() != WL_CONNECTED && attempts < 20) {
    delay(500);
    Serial.print(".");
    attempts++;
  }
  
  if (WiFi.status() == WL_CONNECTED) {
    Serial.println("\n✅ WiFi conectado");
    Serial.print("IP address: ");
    Serial.println(WiFi.localIP());
    
    // Iniciar cliente NTP
    timeClient.begin();
    timeClient.setTimeOffset(0);
    
    // Iniciar servidor UDP para QCAL-Net
    udp.begin(QCAL_UDP_PORT);
  } else {
    Serial.println("\n⚠️ No se pudo conectar a WiFi");
  }
}

// ================= SISTEMA DE SINCRONIZACIÓN =================
void performInitialSync() {
  Serial.println("🔄 Sincronización inicial...");
  
  // Sincronizar tiempo NTP
  if (WiFi.status() == WL_CONNECTED) {
    timeClient.update();
    Serial.print("Tiempo sincronizado: ");
    Serial.println(timeClient.getFormattedTime());
  }
  
  // Escanear red QCAL
  scanQCALNetwork();
  
  lastSyncTime = millis();
}

void performNetworkSync() {
  Serial.println("🔄 Sincronización de red QCAL...");
  
  // Actualizar tiempo
  if (WiFi.status() == WL_CONNECTED) {
    timeClient.forceUpdate();
  }
  
  // Broadcast de presencia
  broadcastPresence();
  
  // Buscar otros nodos
  discoverNodes();
  
  // Ajustar frecuencia por consenso
  adjustFrequencyByConsensus();
  
  Serial.println("✅ Sincronización completa");
}

// ================= PROTOCOLO QCAL-NET =================
void broadcastPresence() {
  if (WiFi.status() != WL_CONNECTED) return;
  
  StaticJsonDocument<256> presence;
  presence["node_id"] = nodeID;
  presence["frequency"] = currentFrequency;
  presence["coherence"] = currentCoherence;
  presence["ip"] = WiFi.localIP().toString();
  presence["timestamp"] = millis();
  
  String jsonStr;
  serializeJson(presence, jsonStr);
  
  // Broadcast UDP a toda la red
  IPAddress broadcastIP = WiFi.localIP();
  broadcastIP[3] = 255;
  
  udp.beginPacket(broadcastIP, QCAL_UDP_PORT);
  udp.write(jsonStr.c_str());
  udp.endPacket();
  
  Serial.println("📢 Broadcast de presencia enviado");
}

void discoverNodes() {
  // Leer paquetes UDP entrantes
  int packetSize = udp.parsePacket();
  if (packetSize) {
    char packetBuffer[512];
    int len = udp.read(packetBuffer, 511);
    if (len > 0) {
      packetBuffer[len] = 0;
      
      StaticJsonDocument<512> nodeInfo;
      DeserializationError error = deserializeJson(nodeInfo, packetBuffer);
      
      if (!error) {
        String remoteNodeID = nodeInfo["node_id"];
        float remoteFreq = nodeInfo["frequency"];
        float remoteCoherence = nodeInfo["coherence"];
        
        Serial.print("👥 Nodo descubierto: ");
        Serial.print(remoteNodeID);
        Serial.print(" | Frecuencia: ");
        Serial.print(remoteFreq, 4);
        Serial.print(" | Coherencia: ");
        Serial.println(remoteCoherence, 3);
        
        // Si la coherencia es alta, considerar para consenso
        if (remoteCoherence >= QCAL_COHERENCE_THRESHOLD) {
          addToConsensusPool(remoteNodeID, remoteFreq, remoteCoherence);
        }
      }
    }
  }
}

// ================= MANEJO DE COMANDOS =================
void handleSerialCommands() {
  if (Serial.available() > 0) {
    String command = Serial.readStringUntil('\n');
    command.trim();
    handleCommand(command);
  }
}

void handleCommand(String command) {
  Serial.print("⚡ Comando recibido: ");
  Serial.println(command);
  
  if (command.startsWith("FREQ:")) {
    float newFreq = command.substring(5).toFloat();
    if (newFreq > 0 && newFreq < 1000000) {
      setFrequency(newFreq);
    }
  }
  else if (command == "QCAL_F0") {
    setFrequency(QCAL_F0);
  }
  else if (command == "QCAL_RESONANCE") {
    setFrequency(QCAL_RESONANCE);
  }
  else if (command == "QCAL_LOVE") {
    setFrequency(QCAL_LOVE_FIELD);
  }
  else if (command.startsWith("COHERENCE:")) {
    float newCoherence = command.substring(10).toFloat();
    currentCoherence = newCoherence;
    updateCoherenceDisplay();
  }
  else if (command == "SYNC") {
    performNetworkSync();
  }
  else if (command == "STATUS") {
    printStatus();
  }
  else if (command == "SCAN") {
    scanQCALNetwork();
  }
  else {
    Serial.println("Comando no reconocido");
  }
}

// ================= FUNCIONES AUXILIARES =================
String generateNodeID() {
  uint32_t chipId = 0;
  // Extraer 6 bytes del MAC address (48 bits) del ESP32
  for(int i=0; i<17; i=i+8) {
    chipId |= ((ESP.getEfuseMac() >> (40 - i)) & 0xff) << i;
  }
  return "QCAL_NODE_" + String(chipId, HEX);
}

void monitorEnvironmentalCoherence() {
  // Simulación - En implementación real leería sensores
  float simulatedCoherence = 0.9 + (sin(millis() / 10000.0) * 0.1);
  
  if (fabs(simulatedCoherence - currentCoherence) > 0.01) {
    currentCoherence = simulatedCoherence;
    updateCoherenceDisplay();
  }
}

void updateCoherenceDisplay() {
  Serial.print("🌀 Coherencia: Ψ = ");
  Serial.println(currentCoherence, 3);
  
  if (deviceConnected) {
    String cohStr = String(currentCoherence, 3);
    pCoherenceCharacteristic->setValue(cohStr.c_str());
    pCoherenceCharacteristic->notify();
  }
}

void scanQCALNetwork() {
  Serial.println("🔍 Escaneando red QCAL...");
  broadcastPresence();
  
  // Escuchar respuestas por 2 segundos
  unsigned long scanStart = millis();
  while (millis() - scanStart < 2000) {
    discoverNodes();
    delay(100);
  }
}

void adjustFrequencyByConsensus() {
  Serial.println("🎯 Ajustando frecuencia por consenso...");
  calculateConsensusFrequency();
}

void printStatus() {
  Serial.println("\n📊 ESTADO DEL NODO QCAL ∞³");
  Serial.println("==========================");
  Serial.print("ID: ");
  Serial.println(nodeID);
  Serial.print("Frecuencia actual: ");
  Serial.print(currentFrequency, 4);
  Serial.println(" Hz");
  Serial.print("Coherencia: Ψ = ");
  Serial.println(currentCoherence, 3);
  Serial.print("WiFi: ");
  Serial.println(WiFi.status() == WL_CONNECTED ? "Conectado" : "Desconectado");
  Serial.print("BLE: ");
  Serial.println(deviceConnected ? "Conectado" : "Esperando");
  Serial.print("Última sincronización: ");
  Serial.print((millis() - lastSyncTime) / 1000);
  Serial.println(" segundos");
  Serial.println("==========================\n");
}

// Variables para consenso
struct NodeConsensus {
  String id;
  float frequency;
  float coherence;
};

NodeConsensus consensusPool[10];
int consensusCount = 0;

void addToConsensusPool(String id, float freq, float coh) {
  if (consensusCount < 10) {
    consensusPool[consensusCount].id = id;
    consensusPool[consensusCount].frequency = freq;
    consensusPool[consensusCount].coherence = coh;
    consensusCount++;
  }
}

void calculateConsensusFrequency() {
  if (consensusCount == 0) return;
  
  float totalWeightedFreq = 0;
  float totalWeight = 0;
  
  for (int i = 0; i < consensusCount; i++) {
    float weight = consensusPool[i].coherence;
    totalWeightedFreq += consensusPool[i].frequency * weight;
    totalWeight += weight;
  }
  
  float consensusFreq = totalWeightedFreq / totalWeight;
  
  // Solo ajustar si la diferencia es significativa
  if (fabs(consensusFreq - currentFrequency) > 0.0001) {
    Serial.print("🔄 Ajustando frecuencia por consenso: ");
    Serial.print(consensusFreq, 4);
    Serial.println(" Hz");
    setFrequency(consensusFreq);
  }
  
  // Reset pool
  consensusCount = 0;
}
