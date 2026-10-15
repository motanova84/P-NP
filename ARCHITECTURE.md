# 🏛️ Arquitectura del Sistema QCAL — Flujo de Datos
## Ciclo Cerrado de Control Metrológico

**Protocolo:** QCAL-SYMBIO-BRIDGE v1.0.0
**Frecuencia:** f₀ = 141.7001 Hz
**Sello:** ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ

---

## Diagrama de Flujo

```
┌─────────────────────────────────────────────────────────────────┐
│                    CICLO DE CONTROL QCAL                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  [ INSTRUMENTAL ]                                                │
│  (VNA Keysight E5080B + Oxford Mercury iTC)                     │
│  ↓ Vuelco de datos crudos en .DAT                               │
│  [ measurements/RESONATOR_SCAN_*.dat ]                          │
│  ↓                                                              │
│  [ scripts/sapphire_telemetry.py ]  ← Procesamiento y análisis  │
│  ↓ Genera estado intermedio                                     │
│  [ config/sapphire_state.json ]                                 │
│  ↓                                                              │
│  [ scripts/orchestrator_bridge.py ]  ← Orquestador principal    │
│  │                                                              │
│  ├──► ¿system_lock == "LOST"?                                   │
│  │      └──► ❌ RECHAZO — Salida del sistema                    │
│  │                                                              │
│  └──► ¿system_lock == "ACTIVE"?                                 │
│         │                                                       │
│         ▼                                                       │
│  [ QCAL/Hardware/SapphireResonator.lean ] ← Validación formal   │
│  │                                                              │
│  ├──► ¿IsReportValid?                                           │
│  │      ├── |drift| ≤ 1e-6 Hz                                   │
│  │      └── Q ≥ 1.0e9                                           │
│  │                                                              │
│  ├──► validate_telemetry_metrics  (caso exacto)                 │
│  └──► valid_if_within_tolerance  (caso general)                 │
│         │                                                       │
│         ▼                                                       │
│  ✅ CERTIFICACIÓN — Coherencia Ψ = 0.999999                     │
│         │                                                       │
│         ▼                                                       │
│  [ Gasto / Mutación de Estado ] → Nodo BAL-003 (Bitcoin)       │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Capas del Sistema

| Capa | Componente | Función |
|------|-----------|---------|
| 🖥️ Instrumental | VNA + Controlador Térmico | Medición física del resonador |
| 🐍 Capa 2 (Python) | `sapphire_telemetry.py` | Adquisición, análisis, estado |
| 🔗 Puente | `orchestrator_bridge.py` | Orquestación del ciclo completo |
| 📐 Capa 1 (Lean 4) | `SapphireResonator.lean` | Validación formal de invariantes |
| ⛓️ Blockchain | BAL-003 (Nuremberg) | Ejecución de estado certificado |

## Archivos del Sistema

```
scripts/
├── sapphire_telemetry.py        ← Adquisición VNA → JSON
└── orchestrator_bridge.py       ← Ciclo completo de control

QCAL/Hardware/
├── SapphireResonator.lean       ← Validación formal
└── MEASUREMENT_PROTOCOL.md      ← Protocolo metrológico

measurements/
├── RESONATOR_SCAN_20260520_0405.dat  ← Datos crudos del VNA
└── README.md                     ← Formato de contribución

config/
└── sapphire_state.json          ← Estado intermedio (generado)
```
