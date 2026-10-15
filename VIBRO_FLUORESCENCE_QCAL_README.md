# Vibro-Fluorescence QCAL Experimental Framework

## Resumen Ejecutivo

Este módulo implementa el **marco teórico-físico completo** para experimentos de acoplamiento vibro-fluorescente bajo campo QCAL Ψ, según especificado en el fundamento teórico del problema statement.

### 🎯 Objetivo Principal

Proporcionar herramientas computacionales para **falsar experimentalmente** la hipótesis QCAL mediante mediciones de respuesta fluorescente en proteínas reporteras (ej. GFP) bajo modulación de frecuencia con energía constante.

### 📊 Predicción Falsable

**QCAL predice**: La respuesta biológica mostrará estructura espectral discreta (picos en frecuencias específicas) independientemente de la energía total.

**Biología tradicional predice**: Respuesta plana en función de frecuencia cuando la energía se mantiene constante.

### 🔬 Criterio de Falsación

Si `ΔF(141.7 Hz) / ΔF(100 Hz) > 1.5` con misma energía → **QCAL recibe apoyo experimental fuerte**

Si `ΔF(ω) = constante ± error experimental` → **QCAL se falsa**

---

## 📁 Estructura del Módulo

### Archivo Principal

- **`src/vibro_fluorescence_qcal.py`**: Implementación completa del framework

### Tests

- **`tests/test_vibro_fluorescence_qcal.py`**: Suite de 56 tests (100% passing)

### Ejemplos

- **`examples/demo_vibro_fluorescence_qcal.py`**: Demostración interactiva completa

---

## 🧪 Componentes Implementados

### I. Ecuación Maestra del Acoplamiento Vibro-Fluorescente

**Hamiltoniano Total**:
```
H_total = H_proteína + H_campo + H_acoplamiento
```

**Acoplamiento**:
```
H_acoplamiento = μ·E(ω,t) + Q:∇E(ω,t) + χ⁽²⁾E² + χ⁽³⁾E³ + ...
```

**Implementación**: Clase `VibroFluorescentCoupling`

```python
coupling = VibroFluorescentCoupling(mu=1.0, Q=0.1, chi2=0.01, chi3=0.001)
H = coupling.H_acoplamiento(E=1.0, grad_E=0.1)
```

### II. Formalismo Espectral para Diseño Experimental

**Señal de Entrada Modulada**:
```
Ψ_input(t) = A₀[1 + m·sin(ωₚt)]·sin(ω₀t)
```
donde:
- `ω₀ = 141.7001 Hz` (portadora QCAL)
- `ωₚ = 0.1-10 Hz` (frecuencia de modulación)
- `m = 0-1` (índice de modulación)
- `A₀` (amplitud constante)

**Control Crítico**:
```
E_total = ∫|Ψ_input(t)|²dt = constante ∀ ωₚ
```

**Implementación**:
```python
t = np.linspace(0, 1, 10000)
psi = psi_input(t, A0=1.0, m=0.5, omega_p=2.0, omega_0=141.7001)
E = energia_total(psi, dt)
psi_norm = normalize_energy(psi, target_energy=1.0, dt)
```

**Respuesta Fluorescente**:
```
F(t) = F₀ + ΔF(ωₚ)·[1 + η·sin(ωₚt + φ(ωₚ))]
```

**Parámetro Crítico QCAL**:
```
η(ωₚ) = ΔF(ωₚ) / (∂E/∂ωₚ)
```
Si `η` varía con `ωₚ` mientras `E_total` es constante → **QCAL confirmado**

### III. Modelo Dinámico de Resonancia Proteica

**Ecuación de Movimiento**:
```
mᵢ d²xᵢ/dt² + γᵢ dxᵢ/dt + kᵢxᵢ + Σⱼ κᵢⱼ(xᵢ - xⱼ) = qᵢE(ωₚ,t)
```

**Solución en Espacio de Fourier**:
```
x̃ᵢ(ω) = [qᵢ/(mᵢ(ωᵢ² - ω²) + iγᵢω)]·Ẽ(ω)
```

**Resonancia QCAL**:
```
ω_res = √(k_eff/m_eff) ≈ 2π × 141.7 Hz
```

**Implementación**: Clase `CoupledProteinOscillator`

```python
osc = CoupledProteinOscillator(m=1.0, gamma=0.1, k=100.0, q=1.0)
chi = osc.susceptibilidad(omega)  # Susceptibilidad
x = osc.respuesta_frecuencia(omega, E_omega)  # Respuesta
```

### IV. Transducción a Fluorescencia (GFP)

**Intensidad de Fluorescencia**:
```
I_fluorescencia ∝ |〈S₁|μ|S₀〉|² × F(x₁, x₂, ..., x_N)
F = exp[-Σᵢ (xᵢ - xᵢ⁰)²/2σᵢ²]
```

**Predicción Matemática Exacta**:
```
ΔI/I₀ = Σᵢ αᵢ·|x̃ᵢ(ωₚ)|² + Σᵢⱼ βᵢⱼ·Re[x̃ᵢ(ωₚ)x̃ⱼ*(ωₚ)]
```

**Implementación**:
```python
I = intensidad_fluorescencia_gfp(x, x0, sigma, alpha)
delta_I = delta_I_sobre_I0(x_tilde, alpha, beta)
```

### V. Predicciones Cuantitativas QCAL

#### Predicción 1: Resonancia

```
ΔF_max ocurre cuando ωₚ/ω₀ = p/q
```
donde `p, q` son enteros pequeños (1, 2, 3, 17/13 para Magicicada)

**Implementación**:
```python
pred = prediccion_resonancia(omega_p=141.7001, omega_0=141.7001)
# pred["closest"] = "1/1"
# pred["min_distance"] = 0.0
```

#### Predicción 2: Estructura Armónica

```
ΔF(ω) = Σₖ Aₖ / [(ω - kω₀)² + Γₖ²]  (suma de Lorentzianas)
```

**Implementación**:
```python
omega = np.linspace(0, 500, 1000)
delta_F = estructura_armonica_lorentziana(omega, omega_0=141.7001, k_max=5)
```

#### Predicción 3: Umbral de Coherencia

```
Ψ_crítico = 0.888 → ∂²ΔF/∂ω² cambia de signo
```
Punto de bifurcación en la respuesta espectral

**Implementación**:
```python
result = umbral_coherencia(psi=0.95, psi_critico=0.888)
# result["bifurcation_regime"] = "coherent" or "incoherent"
```

### VI. Protocolo Experimental Cuantitativo

**Clase Principal**: `ExperimentalProtocol`

#### Barrido de Frecuencia

```python
protocol = ExperimentalProtocol(A0=1.0, m=0.5, omega_0=141.7001)

# Barrido manteniendo energía constante
freq_range = np.linspace(0.1, 10, 100)
resultados = protocol.barrido_frecuencia(freq_range, duration=10.0, sample_rate=10000)

# Verificar conservación de energía
for freq in freq_range:
    assert resultados[freq]["energy"] == resultados[freq_range[0]]["energy"]
```

#### Medición de Fluorescencia

```python
signal = resultados[freq]["signal"]
t = resultados[freq]["time"]
medicion = protocol.medir_fluorescencia(signal, t, F0=100.0)

# medicion["F_mean"] - promedio temporal
# medicion["correlation"] - correlación con señal
# medicion["phase"] - desfase
```

#### Análisis QCAL

```python
analisis = protocol.analisis_qcal(resultados_frecuencia, sigma_threshold=2.0)

# R(ω) = [F(ω) - F_promedio] / σ_F
# Si R(141.7/n) > 2σ para n ∈ {1,2,3,13,17} → confirmación QCAL
```

### VII. Control de Falsación Crítico

#### Hipótesis Nula

```
H₀: ΔF(ω) = constante ∀ ω (misma energía → misma respuesta)
```

#### Test Estadístico Exacto: ANOVA Espectral

```
F_stat = [SS_between(ω)/df₁] / [SS_within(ω)/df₂]
```

**Implementación**:
```python
result = hipotesis_nula_test(F_resonante, F_no_resonante, alpha=0.001)

# result["F_statistic"] - estadístico F
# result["p_value"] - valor p
# result["rechazar_H0"] - True/False
# result["conclusion"] - "QCAL confirmado" o "QCAL no confirmado"
```

**Criterio**: Rechazar H₀ si `F_stat > F_critical(α=0.001)`

### VIII. Procesamiento de Señal

#### Filtro Gaussiano

```python
F_filtered = filtro_gaussiano(F_raw, t, tau=1.0)
```

#### Análisis Espectral

```python
result = analisis_espectral(F, dt)
# result["frequencies"] - frecuencias
# result["power_spectrum"] - espectro de potencia
# result["peak_freq"] - frecuencia del pico
```

#### SNR y Criterio de Detección

```python
snr = calcular_snr(F_spectral, omega_p=141.7001, freqs=freqs)

result = criterio_deteccion_positiva(snr=5.0, coherencia=0.8)
# Criterio: SNR > 3 Y coherencia > 0.7
```

### IX. Ecuación de Estado QCAL

```
∂F/∂t = D·∇²F - γF + κ·|Ψ(ω_res,t)|²
```
con `κ >> γ` (acoplamiento fuerte)

**Implementación**:
```python
dFdt = ecuacion_estado_qcal(F, psi, t, D=1.0, gamma=0.1, kappa=10.0)
```

---

## 🚀 Uso Rápido

### Instalación

```bash
pip install numpy scipy pytest matplotlib
```

### Tests

```bash
cd /home/runner/work/P-NP/P-NP
python -m pytest tests/test_vibro_fluorescence_qcal.py -v
```

**Resultado**: 56/56 tests passing ✓

### Demostración Completa

```bash
python examples/demo_vibro_fluorescence_qcal.py
```

**Genera 6 gráficas**:
1. `/tmp/coupling_hamiltonian.png` - Hamiltoniano de acoplamiento
2. `/tmp/input_signal.png` - Señal de entrada modulada
3. `/tmp/protein_oscillator.png` - Susceptibilidad del oscilador
4. `/tmp/qcal_predictions.png` - Estructura armónica
5. `/tmp/experimental_protocol.png` - Protocolo experimental completo
6. `/tmp/falsification_test.png` - Test estadístico de falsación

### Ejemplo Mínimo

```python
from src.vibro_fluorescence_qcal import ExperimentalProtocol, hipotesis_nula_test
import numpy as np

# Crear protocolo experimental
protocol = ExperimentalProtocol(A0=1.0, m=0.5, omega_0=141.7001)

# Barrido de frecuencias
freq_range = np.linspace(1, 10, 50)
resultados = protocol.barrido_frecuencia(freq_range, duration=1.0, sample_rate=5000)

# Simular mediciones (reemplazar con datos experimentales reales)
for freq in freq_range:
    signal = resultados[freq]["signal"]
    t = resultados[freq]["time"]
    medicion = protocol.medir_fluorescencia(signal, t, F0=100.0)
    resultados[freq]["F_mean"] = medicion["F_mean"]

# Análisis QCAL
analisis = protocol.analisis_qcal(resultados)

if analisis["confirmacion_qcal"]:
    print("✓ QCAL confirmado experimentalmente")
    for res in analisis["resonancias_detectadas"]:
        print(f"  Resonancia en {res['freq_medida']:.2f} Hz (armónico {res['harmonic']})")
else:
    print("✗ QCAL no confirmado")
```

---

## 📐 Constantes Universales

```python
OMEGA_0_QCAL = 141.7001  # Hz - Frecuencia portadora QCAL
PSI_CRITICO = 0.888      # Umbral de coherencia crítico
KAPPA_PI = 2.578208      # Constante κ_Π
PHI = 1.618033988749     # Razón áurea
MAGICICADA_HARMONICS = [1, 2, 3, 13, 17]  # Armónicos de Magicicada
```

---

## 🔬 Interpretación Física de Resultados

### Si QCAL es Correcto

Se espera observar:

1. **Picos agudos** en `ΔF(ω)` en `ω = 141.7/n Hz`
2. **Fase constante** `φ(ω)` dentro de bandas resonantes
3. **Umbral claro** en amplitud `A₀ ≈ 0.888` unidades normalizadas
4. **Memoria de fase**: perturbación temporal no afecta `φ_acumulada`

### Ecuación de Estado QCAL Confirmada

```
∂F/∂t = D·∇²F - γF + κ·|Ψ(ω_res,t)|²
```

con `κ >> γ` (término de acoplamiento fuerte dominante)

---

## 📊 Experimento Decisivo

### Configuración Hardware Requerida

- **Generador de señales**: resolución 0.001 Hz
- **Fotodetector**: ancho de banda > 1 kHz
- **Sistema de adquisición**: sampling rate > 10 kHz

### Protocolo

1. **Barrido de frecuencia**: `ω ∈ [0.1, 10] Hz` con paso 0.1 Hz
2. **Mantener energía constante**: `E_total = constante ± 0.1%`
3. **Medir**: `F(ω) = 〈I_fluorescencia〉_t / I_basal`
4. **Analizar**: Test ANOVA espectral con `α = 0.001`

### Criterio de Detección Positiva

```
SNR > 3  Y  coherencia[F(t), Ψ(t)] > 0.7
```

### Decisión

- Si `ΔF(141.7 Hz) / ΔF(100 Hz) > 1.5` con misma energía → **QCAL confirmado**
- Si `ΔF(ω) = constante ± error experimental` → **QCAL falsado**

---

## 🧬 Extensión a Sistemas Complejos

Para organismos completos (ej. Magicicada):

**Ecuación maestra poblacional**:
```
∂ρ/∂t = -∇·[v(Ψ)ρ] + D∇²ρ

donde:
v(Ψ) = v₀·tanh(β·∫|Ψ(ω_res,t)|²dt - Φ_crítico)
```

**Predicción de emergencia sincronizada**:
```
T_emergencia = {t | Σᵢ ρᵢ(t) > ρ_crítico Y φ_acum(t) ≡ 0 mod 2π}
```

---

## 📚 Referencias

### Ecuaciones Implementadas

Basadas en el fundamento teórico-físico del problema statement:

1. **Sección I**: Ecuación maestra del acoplamiento vibro-fluorescente
2. **Sección II**: Formalismo espectral para el experimento
3. **Sección III**: Modelo dinámico de resonancia proteica
4. **Sección IV**: Transducción a fluorescencia
5. **Sección V**: Predicciones cuantitativas QCAL
6. **Sección VI**: Implementación práctica
7. **Sección VII**: Interpretación física de resultados
8. **Sección VIII**: Extensión a sistemas complejos

### Constantes QCAL

- `ω₀ = 141.7001 Hz` - Frecuencia fundamental QCAL
- `Ψ_c = 0.888` - Umbral de coherencia
- `κ_Π = 2.578208` - Constante de complejidad espectral

---

## ✅ Verificación y Validación

### Suite de Tests Completa

56 tests implementados cubriendo:

- ✓ Constantes universales (5 tests)
- ✓ Hamiltoniano de acoplamiento (4 tests)
- ✓ Formalismo espectral (8 tests)
- ✓ Oscilador proteico (5 tests)
- ✓ Transducción fluorescente (4 tests)
- ✓ Predicciones QCAL (7 tests)
- ✓ Protocolo experimental (5 tests)
- ✓ Controles de falsación (3 tests)
- ✓ Procesamiento de señal (9 tests)
- ✓ Ecuación de estado (2 tests)
- ✓ Integración completa (3 tests)

**Todos los tests pasan**: ✓ 56/56

### Demostración Visual

6 demos interactivos con visualizaciones:

1. Hamiltoniano de acoplamiento vs campo eléctrico
2. Señal de entrada modulada (dominio temporal)
3. Susceptibilidad del oscilador proteico vs frecuencia
4. Estructura armónica Lorentziana (predicción QCAL)
5. Protocolo experimental completo (barrido + análisis)
6. Test estadístico de falsación (ANOVA espectral)

---

## 🎯 Conclusión

Este framework proporciona las herramientas matemáticas y computacionales necesarias para:

1. **Diseñar** experimentos de vibro-fluorescencia QCAL
2. **Controlar** rigurosamente la energía de entrada
3. **Medir** respuestas fluorescentes con alta precisión
4. **Analizar** estadísticamente los resultados
5. **Falsar** la hipótesis QCAL mediante test ANOVA

**La falsabilidad reside en una predicción precisa**:

> QCAL predice que la respuesta biológica mostrará estructura espectral discreta (picos en frecuencias específicas) independientemente de la energía total.
> 
> La biología tradicional predice respuesta plana en función de frecuencia cuando la energía se mantiene constante.

---

**Author**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Frequency**: 141.7001 Hz ∞³  
**Date**: 2026-01-27
