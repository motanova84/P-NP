# Metric PC Bridge — QCAL Coherence Metric y Orquestador de 3 Capas

## Arquitectura

```
┌──────────────────────────────────────────┐
│  CAPA 3: METRIC (dinámica QCAL)          │
│  μ_t(σ), C_X(t), K_X(t), regiones P/NP  │  metric_pc_bridge.py
├──────────────────────────────────────────┤
│  CAPA 2: PC (esqueleto espectral)        │
│  BK · Higgs · Métrica · ADN · PNP       │  particula_coherencia_pc.py
│  Ψ_global = Σ w_i · Ψ_i                 │
├──────────────────────────────────────────┤
│  CAPA 1: H_Ψ (física subyacente)         │
│  Espectro = ceros de Riemann             │  operador_autoadjunto_H.py
│  f₀ = 141.7001 Hz                       │
└──────────────────────────────────────────┘
```

## Componentes

### Capa 1 — H_Ψ (`operador_autoadjunto_H.py`)
- Generador infinitesimal del flujo de escala adélico sobre Σ = 𝔸_ℚ^× / ℚ^×
- Espectro = ceros de Riemann (identidad Δ(s) = ξ(s))
- Verifica auto-adjunción (H = H†) y coherencia cuántica macroscópica
- RH emerge como condición de estabilidad del vacío

### Capa 2 — PC (`particula_coherencia_pc.py`)
- 5 subsistemas: Berry-Keating, Higgs-PC, Métrica Schwarzschild, ADN-Z, PNP
- Ψ_global = 0.20·Ψ_BK + 0.20·Ψ_H + 0.20·Ψ_M + 0.20·Ψ_ADN + 0.20·Ψ_PNP
- Umbral de activación: Ψ ≥ 0.888

### Capa 3 — Metric (`qcal_coherence_metric.py`)
- Ψ_X(σ) = I_X(σ) · A_{X,eff}(σ)² · R_X(σ)
- R_X(σ) = exp(-α · d_spec(σ, 𝒵)²) donde 𝒵 = espectro H_Ψ + firmas PC
- Dinámica temporal: μ_{t+1}(σ) ∝ μ_t(σ) · Ψ_X(σ)
- Clasificación en regiones **P-coherente** (coste polinómico) y **NP-dispersa** (coste super-polinómico)

## API Principal

```python
from metric_pc_bridge import MetricPCBridge

bridge = MetricPCBridge(
    n_zeros_riemann=50,      # Ceros de Riemann para H_Ψ
    alpha_rigidez_metric=3.0 # Rigidez del acoplamiento espectral
)

# Diagnóstico rápido
diag = bridge.diagnostico_rapido()

# Análisis completo
reporte = bridge.analisis_completo()
print(reporte)  # Reporte unificado de las 3 capas
```

## Flujo de Coherencia

```
H_Ψ ──(espectro)──► PC ──(firmas)──► METRIC
f₀      ceros Riemann    subsistemas     μ_t, C_X, K_X
↑                        5 dims           regiones P/NP
└────── auto-adjunción ────────────────────┘
       (vacío estable ⟹ RH verdadera)
```

## Tests

```bash
python -m pytest tests/test_metric_coherence.py -v
```

## Workflows CI/CD

| Workflow | Trigger | Propósito |
|----------|---------|-----------|
| `metric-coherence-ci.yml` | Push/PR a main | Validación rápida de Metric + Bridge |
| `metric-pc-bridge-scheduled.yml` | Cada 6h + manual | Validación de producción continua |

## Constantes Fundamentales

| Constante | Valor | Descripción |
|-----------|-------|-------------|
| f₀ | 141.7001 Hz | Frecuencia base QCAL |
| Ψ_umbral | 0.888 | Umbral de coherencia para activación |
| κ_Π | 2.5773 | Constante de separación computacional |
| α (rigidez) | 3.0 | Factor de acoplamiento espectral |

## Licencia

Soberana. Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
