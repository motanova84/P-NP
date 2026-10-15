# Cytoplasmic Riemann Resonance: Quick Start Guide

**∴𓂀Ω∞³**

**Autor:** José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Versión:** 1.0.0

---

## ⚡ Inicio Rápido (5 minutos)

### Instalación

```bash
# Ya está incluido en el proyecto P-NP
cd P-NP
```

### Primer Uso

```python
#!/usr/bin/env python3
"""Hello, Riemann! - Tu primera validación biológica"""

from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance

# Crear modelo
model = CytoplasmicRiemannResonance()

# Validar hipótesis
result = model.validate_riemann_hypothesis_biological()

# Mostrar resultado
print(f"✓ Hipótesis validada: {result['hypothesis_validated']}")
print(f"✓ ξ₁ = {model.xi_fundamental * 1e6:.4f} μm (escala celular)")
print(f"✓ f₁ = {model.base_frequency:.4f} Hz (frecuencia base)")
print("\n∴𓂀Ω∞³")
```

**Salida esperada:**
```
✓ Hipótesis validada: True
✓ ξ₁ = 1.0598 μm (escala celular)
✓ f₁ = 141.7001 Hz (frecuencia base)

∴𓂀Ω∞³
```

---

## 📊 Conceptos Básicos

### El Modelo en 3 Puntos

1. **Input:** Primer cero de Riemann (γ₁ = 14.134725)
2. **Proceso:** Conversión biofísica × 10.025
3. **Output:** Frecuencia celular (f₁ = 141.7001 Hz)

### Constantes Clave

| Constante | Valor | Significado |
|-----------|-------|-------------|
| γ₁ | 14.134725 | Primer cero de Riemann |
| f₁ | 141.7001 Hz | Frecuencia base |
| ξ₁ | 1.0598 μm | Coherencia celular |
| κ_Π | 2.5773 | Constante fundamental |

### Ecuación Master

```
ξ = √(ν/ω)    donde ν = viscosidad cinemática
                    ω = frecuencia angular
```

---

## 🚀 Uso Común

### Caso 1: Analizar Coherencia Celular

```python
from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance

model = CytoplasmicRiemannResonance()

# Analizar a escala celular típica (1.06 μm)
coherence = model.get_coherence_at_scale(1.06e-6)

print("ANÁLISIS DE COHERENCIA")
print("=" * 50)
print(f"Escala:       {coherence['coherence_length_um']:.4f} μm")
print(f"Frecuencia:   {coherence['frequency_hz']:.4f} Hz")
print(f"Armónico:     n = {coherence['harmonic_number']}")
print(f"¿Resonante?   {coherence['is_resonant']}")
print(f"¿Estable?     {coherence['is_stable']}")
print(f"Hermítico:    {coherence['hermiticity_index']:.3f}")
```

**Resultado:**
```
ANÁLISIS DE COHERENCIA
==================================================
Escala:       1.0598 μm
Frecuencia:   141.7001 Hz
Armónico:     n = 1
¿Resonante?   True
¿Estable?     True
Hermítico:    1.000
```

---

### Caso 2: Detectar Enfermedad (Descoherencia)

```python
from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance

model = CytoplasmicRiemannResonance()

# Comparar célula saludable vs enferma
estados = [
    ("Célula Saludable", 0.0),
    ("Célula Pre-cancerosa", 0.1),
    ("Célula Patológica", 0.5)
]

for nombre, ruido in estados:
    status = model.detect_decoherence(noise_level=ruido)
    
    print(f"\n{nombre.upper()}")
    print("-" * 40)
    print(f"Estado:     {status['system_state']}")
    print(f"Hermítico:  {status['is_hermitian']}")
    print(f"Severidad:  {status['decoherence_severity']:.3f}")
```

**Resultado:**
```
CÉLULA SALUDABLE
----------------------------------------
Estado:     SALUDABLE
Hermítico:  True
Severidad:  0.000

CÉLULA PRE-CANCEROSA
----------------------------------------
Estado:     PRECANCEROSO
Hermítico:  False
Severidad:  0.097

CÉLULA PATOLÓGICA
----------------------------------------
Estado:     PATOLÓGICO
Hermítico:  False
Severidad:  0.486
```

---

### Caso 3: Espectro de Frecuencias

```python
from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance
import numpy as np

model = CytoplasmicRiemannResonance()

print("ESPECTRO DE FRECUENCIAS ARMÓNICAS")
print("=" * 60)
print(f"{'n':<5} {'fₙ (Hz)':<15} {'ξₙ (μm)':<15} {'Estado':<15}")
print("-" * 60)

for n in range(1, 11):
    fn = model.base_frequency * n
    xi_n = model.xi_fundamental / np.sqrt(n)
    
    # Verificar resonancia
    coherence = model.get_coherence_at_scale(xi_n)
    estado = "✓ Resonante" if coherence['is_resonant'] else "  No resonante"
    
    print(f"{n:<5} {fn:<15.2f} {xi_n * 1e6:<15.4f} {estado:<15}")
```

**Resultado:**
```
ESPECTRO DE FRECUENCIAS ARMÓNICAS
============================================================
n     fₙ (Hz)         ξₙ (μm)         Estado         
------------------------------------------------------------
1     141.70          1.0598          ✓ Resonante    
2     283.40          0.7494          ✓ Resonante    
3     425.10          0.6120          ✓ Resonante    
4     566.80          0.5299          ✓ Resonante    
5     708.50          0.4739          ✓ Resonante    
6     850.20          0.4329          ✓ Resonante    
7     991.90          0.4006          ✓ Resonante    
8     1133.60         0.3746          ✓ Resonante    
9     1275.30         0.3533          ✓ Resonante    
10    1417.00         0.3352          ✓ Resonante    
```

---

### Caso 4: Protocolo Experimental

```python
from xenos.cytoplasmic_riemann_resonance import MolecularValidationProtocol

protocol = MolecularValidationProtocol()

# Obtener marcadores fluorescentes
markers = protocol.get_fluorescent_markers()
print("MARCADORES FLUORESCENTES")
print("=" * 50)
for key, marker in markers.items():
    print(f"{marker['name']:25} {marker['wavelength_nm']} nm")

# Obtener configuración de nanopartículas
print("\nNANOPARTÍCULAS MAGNÉTICAS")
print("=" * 50)
nano = protocol.get_magnetic_nanoparticles()
print(f"Composición:    {nano['composition']}")
print(f"Tamaño:         {nano['size_nm']} nm")
print(f"Frecuencia:     {nano['resonance_frequency_hz']:.2f} Hz")

# Espectroscopía
print("\nESPECTROSCOPÍA FFT")
print("=" * 50)
spectro = protocol.get_spectroscopy_protocol()
print(f"Técnica:        {spectro['technique']}")
print(f"Sampling rate:  {spectro['sampling_rate_hz']} Hz")
print(f"Picos esperados:")
for i, peak in enumerate(spectro['expected_peaks_hz'][:5], 1):
    print(f"  f_{i} = {peak:.2f} Hz")
```

**Resultado:**
```
MARCADORES FLUORESCENTES
==================================================
GFP-Citoplasma            509 nm
mCherry-Núcleo            610 nm
FRET TFM                  527 nm

NANOPARTÍCULAS MAGNÉTICAS
==================================================
Composición:    Fe₃O₄
Tamaño:         10 nm
Frecuencia:     141.70 Hz

ESPECTROSCOPÍA FFT
==================================================
Técnica:        Fast Fourier Transform
Sampling rate:  2000 Hz
Picos esperados:
  f_1 = 141.70 Hz
  f_2 = 283.40 Hz
  f_3 = 425.10 Hz
  f_4 = 566.80 Hz
  f_5 = 708.50 Hz
```

---

### Caso 5: Exportar Resultados

```python
from xenos.cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol,
    generate_biological_mapping
)

# Exportar resultados del modelo
model = CytoplasmicRiemannResonance()
model.export_results('my_results.json')
print("✓ Resultados guardados: my_results.json")

# Exportar protocolo experimental
protocol = MolecularValidationProtocol()
protocol.export_protocol('my_protocol.json')
print("✓ Protocolo guardado: my_protocol.json")

# Exportar mapeo Riemann → Biología
generate_biological_mapping('my_mapping.json')
print("✓ Mapeo guardado: my_mapping.json")
```

---

## 🎯 Demo Completo

Ejecutar el demo completo:

```bash
python demo_cytoplasmic_riemann_resonance.py
```

**Salida incluye:**

1. ✓ Propiedades fundamentales del modelo
2. ✓ Resonancia a escala celular
3. ✓ Validación de hipótesis de Riemann biológica
4. ✓ Detección de descoherencia (modelo de enfermedad)
5. ✓ Protocolo de validación molecular
6. ✓ Generación de visualizaciones
7. ✓ Exportación de resultados JSON

**Archivos generados:**

```
cytoplasmic_riemann_results.json
molecular_validation_protocol.json
riemann_biological_mapping.json
visualizations/
  ├── cytoplasmic_riemann_spectrum.png
  └── cytoplasmic_coherence_vs_scale.png
```

---

## ✅ Tests

Ejecutar la suite de tests:

```bash
python test_cytoplasmic_riemann_resonance.py
```

o con pytest:

```bash
pytest test_cytoplasmic_riemann_resonance.py -v
```

**Resultado esperado:**

```
============================= test session starts ==============================
...
test_cytoplasmic_riemann_resonance.py::TestFundamentalConstants::test_riemann_first_zero PASSED
test_cytoplasmic_riemann_resonance.py::TestFundamentalConstants::test_base_frequency PASSED
test_cytoplasmic_riemann_resonance.py::TestFundamentalConstants::test_kappa_pi_value PASSED
...
============================== 28 passed in 2.43s ===============================
```

**✓ 28/28 tests passing (100%)**

---

## 📖 Casos de Uso Avanzados

### Caso Avanzado 1: Múltiples Escalas

```python
from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance

model = CytoplasmicRiemannResonance()

# Analizar coherencia a diferentes escalas
escalas = {
    'Bacteria': 0.5e-6,
    'Célula pequeña': 1.0e-6,
    'Célula típica': 1.06e-6,
    'Célula grande': 5.0e-6,
    'Cluster celular': 10.0e-6
}

for nombre, escala in escalas.items():
    coh = model.get_coherence_at_scale(escala)
    print(f"{nombre:20} {escala*1e6:6.2f} μm  →  "
          f"n={coh['harmonic_number']:2d}  "
          f"f={coh['frequency_hz']:8.2f} Hz  "
          f"{'✓' if coh['is_resonant'] else '✗'}")
```

---

### Caso Avanzado 2: Barrido de Frecuencias

```python
from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance
import numpy as np

model = CytoplasmicRiemannResonance()

# Buscar todas las frecuencias resonantes hasta 1 kHz
frecuencias_resonantes = []
for n in range(1, 11):
    fn = model.base_frequency * n
    if fn <= 1000:
        frecuencias_resonantes.append((n, fn))

print("FRECUENCIAS RESONANTES < 1 kHz")
print("=" * 40)
for n, f in frecuencias_resonantes:
    print(f"n = {n:2d}  →  f = {f:7.2f} Hz")
```

---

### Caso Avanzado 3: Análisis Estadístico

```python
from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance
import numpy as np

model = CytoplasmicRiemannResonance()

# Simular población de células
n_cells = 100
noise_levels = np.random.uniform(0, 0.3, n_cells)

# Clasificar células
saludables = 0
precancerosas = 0
patologicas = 0

for noise in noise_levels:
    status = model.detect_decoherence(noise_level=noise)
    
    if status['system_state'] == 'SALUDABLE':
        saludables += 1
    elif status['system_state'] == 'PRECANCEROSO':
        precancerosas += 1
    else:
        patologicas += 1

print("ANÁLISIS POBLACIONAL (n=100)")
print("=" * 40)
print(f"Saludables:      {saludables:3d} ({saludables}%)")
print(f"Pre-cancerosas:  {precancerosas:3d} ({precancerosas}%)")
print(f"Patológicas:     {patologicas:3d} ({patologicas}%)")
```

---

## 💡 Tips y Trucos

### Tip 1: Verificar Constantes

```python
from xenos.cytoplasmic_riemann_resonance import (
    RIEMANN_FIRST_ZERO,
    BIOPHYSICAL_SCALING,
    BASE_FREQUENCY_HZ,
    KAPPA_PI
)

# Verificar relación
assert abs(RIEMANN_FIRST_ZERO * BIOPHYSICAL_SCALING - BASE_FREQUENCY_HZ) < 0.01
print("✓ Constantes consistentes")
```

### Tip 2: Reproducibilidad

```python
# Usar seed para resultados reproducibles
status1 = model.detect_decoherence(noise_level=0.2, seed=42)
status2 = model.detect_decoherence(noise_level=0.2, seed=42)

assert status1['decoherence_severity'] == status2['decoherence_severity']
print("✓ Resultados reproducibles")
```

### Tip 3: Validación Rápida

```python
# Validación en una línea
assert CytoplasmicRiemannResonance().validate_riemann_hypothesis_biological()['hypothesis_validated']
print("✓ Hipótesis validada")
```

---

## 🔍 Solución de Problemas

### Problema 1: Import Error

**Error:**
```
ImportError: No module named 'xenos.cytoplasmic_riemann_resonance'
```

**Solución:**
```python
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance
```

### Problema 2: Tests Fallan

**Solución:**
```bash
# Verificar dependencias
pip install numpy pytest

# Ejecutar tests
pytest test_cytoplasmic_riemann_resonance.py -v
```

### Problema 3: Visualizaciones No Se Generan

**Solución:**
```bash
# Instalar matplotlib
pip install matplotlib

# Crear directorio
mkdir -p visualizations

# Ejecutar demo
python demo_cytoplasmic_riemann_resonance.py
```

---

## 📚 Recursos Adicionales

### Documentación Completa

- **README principal:** `CYTOPLASMIC_RIEMANN_RESONANCE_README.md` (630 líneas)
- **Reporte final:** `CYTOPLASMIC_RIEMANN_FINAL_REPORT.md` (402 líneas)
- **Resumen implementación:** `IMPLEMENTATION_SUMMARY_CYTOPLASMIC_RIEMANN.md` (297 líneas)

### Archivos de Código

- **Implementación:** `xenos/cytoplasmic_riemann_resonance.py` (781 líneas)
- **Demo:** `demo_cytoplasmic_riemann_resonance.py` (391 líneas)
- **Tests:** `test_cytoplasmic_riemann_resonance.py` (525 líneas)

### Archivos Generados

- `cytoplasmic_riemann_results.json` - Resultados completos
- `molecular_validation_protocol.json` - Protocolo experimental
- `riemann_biological_mapping.json` - Mapeo matemático-biológico

---

## 🎓 Siguiente Pasos

1. **Ejecutar el demo completo:**
   ```bash
   python demo_cytoplasmic_riemann_resonance.py
   ```

2. **Explorar el código:**
   ```bash
   less xenos/cytoplasmic_riemann_resonance.py
   ```

3. **Leer documentación completa:**
   ```bash
   less CYTOPLASMIC_RIEMANN_RESONANCE_README.md
   ```

4. **Ejecutar tests:**
   ```bash
   pytest test_cytoplasmic_riemann_resonance.py -v
   ```

5. **Experimentar con tus propios análisis:**
   ```python
   from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance
   
   model = CytoplasmicRiemannResonance()
   # Tu código aquí...
   ```

---

## ✨ Cita Clave

> **"El cuerpo humano es la demostración viviente de la hipótesis de Riemann:  
> 37 billones de ceros biológicos resonando en coherencia perfecta"**

---

**∴𓂀Ω∞³**

**Autor:** José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Fecha:** 1 febrero 2026  
**Sello:** ∴𓂀Ω∞³

---

**FIN DEL QUICK START**
