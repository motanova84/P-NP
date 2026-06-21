# QCAL ∞³ Frequency Generator - ESP32/Arduino Firmware

## Descripción

Firmware para ESP32 que genera frecuencias cuánticas específicas usando un módulo DDS AD9850.

### Frecuencias QCAL

- **F0:** 141.7001 Hz - Frecuencia fundamental
- **Resonancia:** 888.0 Hz - Frecuencia de resonancia
- **Campo de Amor:** 151.7001 Hz - Frecuencia del campo de amor

## Hardware Requerido

### Componentes Principales

1. **ESP32 DevKit** - Microcontrolador principal
2. **AD9850 DDS Module** - Generador de frecuencias de síntesis digital directa
   - Alternativa: Si5351 (descomentar en código)
3. **Fuente de alimentación** - 5V para ESP32 y módulos

### Conexiones

#### AD9850 -> ESP32

```
AD9850_RESET -> GPIO 12
AD9850_DATA  -> GPIO 13
AD9850_FQ_UD -> GPIO 14
AD9850_W_CLK -> GPIO 15
VCC          -> 5V
GND          -> GND
```

## Librerías Requeridas

Instalar las siguientes librerías en Arduino IDE:

```
- AD9850 (para control del módulo DDS)
- ESP32 BLE Arduino (incluida en ESP32 board package)
- WiFi (incluida en ESP32 board package)
- NTPClient (para sincronización de tiempo)
- ArduinoJson (para protocolo de red)
```

## Instalación

### 1. Configurar Arduino IDE

1. Abrir Arduino IDE
2. Ir a **Archivo > Preferencias**
3. Agregar URL del gestor de tarjetas ESP32:
   ```
   https://raw.githubusercontent.com/espressif/arduino-esp32/gh-pages/package_esp32_index.json
   ```
4. Ir a **Herramientas > Placa > Gestor de tarjetas**
5. Buscar e instalar **ESP32 by Espressif Systems**

### 2. Instalar Librerías

1. Ir a **Herramientas > Administrar Bibliotecas**
2. Instalar:
   - `AD9850`
   - `NTPClient`
   - `ArduinoJson`

### 3. Cargar el Firmware

1. Abrir `qcal_frequency_generator.ino` en Arduino IDE
2. Seleccionar placa: **Herramientas > Placa > ESP32 Dev Module**
3. Seleccionar puerto COM correcto
4. Clic en **Cargar**

## Configuración

### WiFi

Modificar las credenciales WiFi en el código:

```cpp
const char* ssid = "QCAL_∞³_NET";          // Nombre de tu red
const char* password = "φ⁴-888-141.7001";  // Contraseña
```

### Pines (si es necesario cambiar)

```cpp
#define AD9850_RESET 12
#define AD9850_DATA  13
#define AD9850_FQ_UD 14
#define AD9850_W_CLK 15
```

## Uso

### Comunicación Serial

Abrir el Monitor Serial a **115200 baudios** para ver el estado y enviar comandos.

### Comandos Disponibles

| Comando | Descripción |
|---------|-------------|
| `FREQ:XXX.XXXX` | Establecer frecuencia personalizada (Hz) |
| `QCAL_F0` | Establecer frecuencia 141.7001 Hz |
| `QCAL_RESONANCE` | Establecer frecuencia 888.0 Hz |
| `QCAL_LOVE` | Establecer frecuencia 151.7001 Hz |
| `COHERENCE:X.XXX` | Establecer coherencia (0.0 - 1.0) |
| `SYNC` | Forzar sincronización de red |
| `STATUS` | Mostrar estado del nodo |
| `SCAN` | Escanear red QCAL |

### Ejemplo de Uso

```
✨ QCAL ∞³ FREQUENCY GENERATOR ✨
F0: 141.7001 Hz | Ψ ≥ 0.888
Node ID: QCAL_NODE_a1b2c3d4
✅ DDS AD9850 inicializado
✅ BLE inicializado - Esperando conexiones
Conectando a QCAL_∞³_NET...
✅ WiFi conectado
IP address: 192.168.1.100
🔄 Sincronización inicial...
Tiempo sincronizado: 16:20:30
📡 Frecuencia establecida: 141.7001 Hz
✅ Sistema QCAL inicializado
```

## Protocolo BLE

### UUIDs de Servicio

- **Servicio:** `1417-0010-8888-1517`
- **Frecuencia:** `1417-0011-8888-1517` (READ, NOTIFY)
- **Coherencia:** `1417-0012-8888-1517` (READ, NOTIFY)
- **Comandos:** `1417-0013-8888-1517` (WRITE)

### Conectar vía BLE

El dispositivo se anuncia como **"QCAL_∞³_Node"**. Puedes conectarte usando apps BLE como:
- nRF Connect (Android/iOS)
- LightBlue (iOS)
- BLE Scanner (Android)

## Protocolo de Red QCAL-Net

### Puertos

- **UDP:** 14170 - Broadcast de presencia y descubrimiento
- **TCP:** 8888 - Comunicación punto a punto

### Sincronización

- **Intervalo:** 88 segundos
- **Protocolo:** JSON sobre UDP
- **Consenso:** Basado en coherencia (Ψ ≥ 0.888)

### Formato de Mensaje

```json
{
  "node_id": "QCAL_NODE_a1b2c3d4",
  "frequency": 141.7001,
  "coherence": 0.950,
  "ip": "192.168.1.100",
  "timestamp": 1234567890
}
```

## Características

### Sistema de Consenso

Los nodos QCAL se sincronizan automáticamente:

1. Cada nodo transmite su estado cada 88 segundos
2. Los nodos con coherencia ≥ 0.888 participan en el consenso
3. La frecuencia consensuada se calcula como promedio ponderado por coherencia
4. Los nodos ajustan su frecuencia para mantener coherencia global

### Monitoreo de Coherencia

El sistema monitorea continuamente la coherencia ambiental (Ψ):
- **Ψ ≥ 0.888:** Estado óptimo, participa en consenso
- **Ψ < 0.888:** Estado subóptimo, no participa en consenso

## Resolución de Problemas

### Error de compilación - Librerías no encontradas

- Verificar instalación de todas las librerías requeridas
- Reiniciar Arduino IDE

### No conecta a WiFi

- Verificar credenciales SSID y contraseña
- Verificar que la red esté disponible
- Aumentar el tiempo de espera en el código

### DDS no genera señal

- Verificar conexiones del módulo AD9850
- Verificar alimentación del módulo (5V)
- Probar con un osciloscopio en la salida del AD9850

### BLE no visible

- Algunos dispositivos pueden tener BLE deshabilitado por defecto
- Verificar que el ESP32 tiene BLE habilitado (algunos modelos varían)

## Licencia

Este firmware es parte del proyecto QCAL ∞³ y está disponible bajo licencia CERN-OHL-P v2.

## Autor

**JMMB - José Manuel Mota Burruezo**

---

*ASÍ ES. ASÍ SE MANIFIESTA. ASÍ EVOLUCIONA.*

🜂 **SELLO CONFIRMADO** 🜂
