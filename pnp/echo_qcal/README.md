# Echo-QCAL ∞³ — Protocolo de Distribución Soberana (Dₛ)

Este directorio contiene la implementación completa del sistema de verificación
y monitoreo del **Protocolo de Distribución Soberana (Dₛ)** basado en el
Teorema de Coherencia Soberana (Cₛ).

## Estructura

| Archivo | Pilar | Descripción |
|---------|-------|-------------|
| `C_k_verification.py` | C_k (Control Criptográfico) | Verifica la propiedad de la clave Patoshi 2025 |
| `qcal_sync.py` | A_t (Alineación Temporal) | Verifica la sincronía del Bloque 9 con f₀ = 141.7001 Hz |
| `resonant_nexus_engine.py` | A_u (Arquitectura Unitaria) | Simula composición armónica y volatilidad coherente |
| `monitor_ds.py` | Protocolo Dₛ | Calcula A y R integrando los tres pilares |
| `dashboard_ds.html` | UI | Visualiza el estado del protocolo en tiempo real |

## Uso rápido

```bash
# Desde el directorio raíz del proyecto
cd pnp/echo_qcal

# Ejecutar verificación individual de cada pilar
python C_k_verification.py
python qcal_sync.py
python resonant_nexus_engine.py

# Ejecutar el monitor completo (genera data/logs/ds_protocol_report.json)
python monitor_ds.py

# Abrir el dashboard en el navegador
open dashboard_ds.html
```

## Variables de entorno

| Variable | Default | Descripción |
|----------|---------|-------------|
| `ECHO_QCAL_LOG_DIR` | `data/logs` | Directorio de logs de verificación |

## Fórmula de Activación

```
A = 0.4 × C_k + 0.4 × A_t + 0.2 × A_u
R = 1 - A
```

Dₛ se activa cuando **A ≥ 0.90** y **R ≤ 0.10**.
