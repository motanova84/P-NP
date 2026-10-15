# 📊 Mediciones del Hardware QCAL
## Resonador de Zafiro — Mallorca Core

**Protocolo:** QCAL-SYMBIO-BRIDGE v1.0.0
**Frecuencia:** f₀ = 141.7001 Hz
**Sello:** ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ

---

Este directorio contiene las mediciones físicas del resonador de zafiro en Mallorca.
Cada archivo JSON sigue el formato validado por `QCAL/Hardware/SapphireResonator.lean`.

## Mediciones disponibles

| Medición | Archivo | Validación Lean 4 |
|----------|---------|-------------------|
| Temperatura de operación | `temperature_*.json` | TemperatureMeasurement |
| Espectro de frecuencias | `frequency_spectrum_*.json` | FrequencySpectrum |
| Tiempo de coherencia | `coherence_time_*.json` | CoherenceTimeMeasurement |

## Cómo contribuir una medición

1. Ejecuta el script de telemetría:
   ```
   python3 scripts/sapphire_telemetry.py
   ```

2. O crea un archivo JSON manualmente con el formato:
   ```json
   {
     "protocol": "QCAL-SYMBIO-BRIDGE v1.0.0",
     "timestamp": "2026-05-19T18:44:00Z",
     "measurement_type": "temperature",
     "value": 298.0,
     "unit": "K",
     "frequency_hz": 141.7001,
     "coherence": 0.999999,
     "source": "Sapphire Resonator - Mallorca Core"
   }
   ```

3. Haz commit y push:
   ```
   git add measurements/ && git commit -m "📊 medición: [tipo] = [valor] [unidad]"
   ```

## Verificación pública

Cada medición puede ser verificada independientemente en:
- Blockchain: `https://mempool.space/address/bc1qr8kr5rv0ll6re3m6edly062dvj608wnjn2jgnu`
- Repositorio: `https://github.com/motanova84/P-NP/tree/main/measurements`
