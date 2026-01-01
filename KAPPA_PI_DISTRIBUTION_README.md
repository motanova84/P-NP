# Análisis de Distribución κ_Π para Variedades Calabi-Yau

## Descripción General

Este módulo implementa el análisis completo de la distribución de la constante κ_Π para variedades Calabi-Yau, tal como se describe en el problema statement del proyecto P-NP.

## ¿Qué es κ_Π?

Para cada variedad Calabi-Yau con números de Hodge (h¹¹, h²¹):
- **N = h¹¹ + h²¹** (número total de moduli)
- **κ_Π = log₂(N)** 

Esta constante conecta la geometría algebraica de las variedades CY con la complejidad computacional del problema P vs NP.

## Archivos del Módulo

### 1. `src/kappa_pi_distribution.py`
Módulo principal con todas las funciones de análisis:

#### Funciones Principales

**`compute_kappa_distribution(cy_list, base=2)`**
- Calcula κ_Π para todas las variedades en `cy_list`
- Retorna: (kappas, Ns, stats)
  - `kappas`: Lista de valores κ_Π
  - `Ns`: Lista de valores N = h¹¹ + h²¹
  - `stats`: Diccionario con estadísticas completas

**`plot_kappa_distribution(kappas, Ns, special_kappa, save_path, show)`**
- Genera visualización de dos paneles:
  - Histograma de densidad de κ_Π
  - Scatter plot N vs κ_Π (escala logarítmica)
- Destaca valores especiales (ej: log₂(13) ≈ 3.700)

**`analyze_local_density(Ns, target_N=13, window=2)`**
- Analiza densidad local alrededor de un valor específico de N
- Detecta anomalías comparando con distribución esperada
- Retorna ratio observado/esperado

**`generate_scientific_report(kappas, Ns, stats)`**
- Genera reporte científico completo formateado
- Responde las 4 preguntas científicas clave

**`compare_with_theoretical_distribution(Ns, model)`**
- Compara distribución observada con modelos teóricos
- Modelos soportados: 'exponential' y 'lognormal'

### 2. `examples/demo_kappa_distribution.py`
Script de demostración completo que muestra:
- Generación de datos realistas de CY
- Análisis estadístico completo
- Comparación con modelos teóricos
- Respuestas a preguntas científicas
- Visualización automática

### 3. `tests/test_kappa_distribution.py`
Suite completa de pruebas unitarias e integración

## Uso Rápido

### Opción 1: Ejecutar el Demo

```bash
python examples/demo_kappa_distribution.py
```

Esto genera:
- Análisis completo en consola
- Gráfico guardado en `output/kappa_pi_distribution.png`
- Respuestas a las 4 preguntas científicas

### Opción 2: Usar el Módulo Directamente

```python
from src.kappa_pi_distribution import (
    compute_kappa_distribution,
    plot_kappa_distribution,
    generate_scientific_report
)

# Tus datos de variedades CY
cy_list = [
    (7, 6),    # h11=7, h21=6 → N=13
    (10, 20),  # h11=10, h21=20 → N=30
    (5, 5),    # h11=5, h21=5 → N=10
    # ... más variedades
]

# Calcular distribución
kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)

# Generar reporte
report = generate_scientific_report(kappas, Ns, stats)
print(report)

# Visualizar
plot_kappa_distribution(
    kappas, 
    Ns, 
    special_kappa=stats['special_N13_kappa'],
    save_path='output/my_analysis.png'
)
```

### Opción 3: Ejecutar el Módulo como Script

```bash
python src/kappa_pi_distribution.py
```

Ejecuta un análisis de ejemplo con 150 variedades simuladas.

## Las 4 Preguntas Científicas

El módulo responde sistemáticamente:

### 1️⃣ ¿La distribución de κ_Π es suave o hay clustering?
- **Métrica**: Coeficiente de Variación (CV = σ/μ)
- **Criterio**: 
  - CV < 0.3 → Clustering fuerte
  - CV < 0.5 → Clustering moderado
  - CV ≥ 0.5 → Distribución dispersa

### 2️⃣ ¿Existe anomalía cerca de log₂(13) ≈ 3.700?
- **Análisis**: Densidad local comparada con modelo exponencial
- **Criterio**: Ratio observado/esperado > 2.0 → Anomalía
- **Resultado**: Indica si N=13 es estadísticamente especial

### 3️⃣ ¿Cuál es la media y desviación estándar?
- **Métricas**: μ(κ_Π), σ(κ_Π)
- **Intervalo**: [μ-σ, μ+σ]
- **Percentiles**: P10, P25, P50, P75, P90

### 4️⃣ ¿Qué tan raras son las CY con N = 13?
- **Frecuencia**: Proporción de variedades con N=13
- **Clasificación**:
  - < 0.5% → Muy raro
  - 0.5-2% → Raro
  - 2-5% → Poco común
  - > 5% → Común

## Análisis de Densidad Local (Bonus)

Para evaluar si N=13 es anómalo:

```python
from src.kappa_pi_distribution import analyze_local_density

density = analyze_local_density(Ns, target_N=13, window=2)

print(f"Densidad observada: {density['exact_density']:.6f}")
print(f"Densidad esperada: {density['expected_density']:.6f}")
print(f"Ratio: {density['anomaly_ratio']:.2f}x")
print(f"¿Anómalo? {density['is_anomalous']}")
```

## Modelos Teóricos

### Modelo Exponencial
```
P(N) ~ exp(-αN)
```
donde α = 1/⟨N⟩

### Modelo Log-Normal
```
log(N) ~ Normal(μ, σ)
```

Ejemplo de comparación:
```python
from src.kappa_pi_distribution import compare_with_theoretical_distribution

# Comparar con exponencial
exp_result = compare_with_theoretical_distribution(Ns, model='exponential')
print(f"α = {exp_result['alpha']:.6f}")
print(f"χ² = {exp_result['chi_squared']:.4f}")

# Comparar con log-normal
lognorm_result = compare_with_theoretical_distribution(Ns, model='lognormal')
print(f"μ = {lognorm_result['mu']:.4f}")
print(f"σ = {lognorm_result['sigma']:.4f}")
```

## Salida del Análisis

El reporte científico incluye:

```
╔══════════════════════════════════════════════════════════════════════════╗
║           ANÁLISIS DE DISTRIBUCIÓN κ_Π - VARIEDADES CALABI-YAU          ║
╚══════════════════════════════════════════════════════════════════════════╝

📊 ESTADÍSTICAS GLOBALES
  Total de Variedades CY:     500
  κ_Π = log₂(h11 + h21):
    • Media:                  5.5268
    • Desviación Estándar:    1.6006
    • Mediana:                5.3219
    • Mínimo:                 2.3219
    • Máximo:                 9.4959

🔍 ANÁLISIS ESPECIAL: N = 13
  κ_Π teórico (log₂(13)):    3.7004
  Ocurrencias de N=13:        31
  Densidad (N=13):           0.062000 (6.20%)
  ...

🎯 PREGUNTAS CIENTÍFICAS RESPONDIDAS
  1. ¿La distribución de κ_Π es suave o hay clustering?
  2. ¿Existe anomalía cerca de log₂(13) ≈ 3.700?
  3. ¿Cuál es la media y desviación estándar?
  4. ¿Qué tan raras son las CY con N = 13?

📝 CONCLUSIÓN CIENTÍFICA
  [Basada en los datos analizados]
```

## Visualizaciones

El módulo genera gráficos de dos paneles:

### Panel Izquierdo: Histograma de κ_Π
- Densidad de probabilidad
- Línea vertical roja en log₂(13) ≈ 3.700
- Permite identificar clustering visual

### Panel Derecho: Scatter N vs κ_Π
- Escala logarítmica en X
- Muestra relación entre N y κ_Π
- Permite identificar outliers

## Pruebas

Ejecutar tests:
```bash
pytest tests/test_kappa_distribution.py -v
```

Tests incluidos:
- ✅ Casos simples con valores conocidos
- ✅ Detección de N=13
- ✅ Manejo de lista vacía
- ✅ Diferentes bases de logaritmo
- ✅ Cálculos estadísticos
- ✅ Análisis de densidad local
- ✅ Detección de anomalías
- ✅ Comparación con modelos teóricos
- ✅ Workflow completo de integración
- ✅ Estabilidad numérica

## Conclusión Científica

Este módulo permite responder la pregunta fundamental:

> **¿La "coherencia espectral" en N=13 es genuina o trivial?**

**Sin análisis de TODA la base de datos**, cualquier proclamación de coherencia espectral es prematura. Este módulo proporciona las herramientas para:

1. ✅ Calcular κ_Π para TODO el conjunto de variedades CY
2. ✅ Analizar la distribución estadística completa
3. ✅ Comparar con modelos teóricos (P(N) ~ exp(-αN))
4. ✅ Detectar anomalías genuinas vs. fluctuaciones
5. ✅ Generar reportes científicos rigurosos

## Requisitos

```
numpy>=1.21
scipy>=1.7
matplotlib>=3.7
```

## Autor

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
Fecha: 1 enero 2026

## Referencias

- Problema statement original: Ver issue principal del proyecto
- Documentación P-NP: Ver README.md principal
- κ_Π Millennium Constant: Ver KAPPA_PI_MILLENNIUM_CONSTANT.md
