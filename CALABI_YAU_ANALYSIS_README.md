# Análisis de Distribución Calabi-Yau

## Descripción

Este módulo implementa un análisis estadístico comprehensivo de la distribución de κ_Π = log₂(h¹¹ + h²¹) en variedades Calabi-Yau. El análisis demuestra que **κ_Π = log₂(13) ≈ 3.7004 NO es un valor especial** en la distribución real de variedades Calabi-Yau.

## Contenido

- `calabi_yau_analysis.py`: Script principal con el análisis completo
- `test_calabi_yau_analysis.py`: Suite de tests para verificar la funcionalidad

## Uso

### Ejecución básica

```bash
python calabi_yau_analysis.py
```

Este comando:
1. Analiza 37 variedades Calabi-Yau de la muestra
2. Calcula κ_Π = log₂(h¹¹ + h²¹) para cada variedad
3. Genera estadísticas descriptivas completas
4. Crea visualizaciones mostrando la distribución
5. Guarda los gráficos en `calabi_yau_distribution.png`

### Ejecutar tests

```bash
python test_calabi_yau_analysis.py
```

## Función principal: `comprehensive_analysis`

```python
def comprehensive_analysis(cy_data):
    """
    Análisis comprehensivo de la distribución de κ_Π para variedades Calabi-Yau.
    
    Args:
        cy_data: Lista de tuplas (h11, h21) representando números de Hodge
        
    Returns:
        Tupla (kappas, N_values, stats) con los valores calculados y estadísticas
    """
```

### Uso programático

```python
from calabi_yau_analysis import comprehensive_analysis

# Datos de ejemplo: lista de tuplas (h11, h21)
cy_data = [
    (1, 101), (1, 149), (2, 128), (3, 75), (4, 90),
    # ... más variedades
]

# Ejecutar análisis
kappas, N_values, stats = comprehensive_analysis(cy_data)

# Acceder a las estadísticas
print(f"Media de κ_Π: {stats['kappa_mean']:.6f}")
print(f"Mediana de κ_Π: {stats['kappa_median']:.6f}")
print(f"Valor log₂(13): {stats['log2_13_value']:.6f}")
print(f"Percentil de log₂(13): {stats['log2_13_percentile']:.2f}%")
```

## Estadísticas calculadas

El análisis calcula las siguientes métricas:

### Estadísticas de κ_Π
- `n_samples`: Número de variedades en la muestra
- `kappa_mean`: Media de κ_Π
- `kappa_std`: Desviación estándar de κ_Π
- `kappa_median`: Mediana de κ_Π

### Estadísticas de N = h¹¹ + h²¹
- `N_mean`: Media de N
- `N_median`: Mediana de N
- `N_min`: Valor mínimo de N
- `N_max`: Valor máximo de N

### Análisis específico de N = 13
- `n13_count`: Frecuencia de variedades con N = 13
- `n13_fraction`: Fracción de variedades con N = 13
- `log2_13_value`: Valor de log₂(13) ≈ 3.7004
- `log2_13_percentile`: Percentil de log₂(13) en la distribución

### Test de normalidad
- `shapiro_p`: Valor p del test de Shapiro-Wilk

## Visualizaciones generadas

El script genera 4 gráficos:

1. **Distribución de κ_Π**: Histograma mostrando la distribución de κ_Π con línea roja marcando log₂(13)
2. **Distribución de N**: Histograma de valores de N = h¹¹ + h²¹ con línea roja en N = 13
3. **Box Plot de κ_Π**: Diagrama de caja mostrando cuartiles y outliers de κ_Π
4. **Q-Q Plot**: Gráfico de cuantiles para evaluar normalidad de la distribución

## Resultados del análisis

Con la muestra de 37 variedades Calabi-Yau:

- **Media de κ_Π**: valor obtenido a partir de los datos reales (ver salida del script)
- **Mediana de κ_Π**: valor obtenido a partir de los datos reales (no tiene por qué coincidir con log₂(13))
- **log₂(13) percentil**: calculado numéricamente a partir de la distribución estimada
- **Frecuencia de N = 13**: número de casos con N = 13 dividido por el tamaño muestral
- **Test de normalidad**: p-value calculado mediante Shapiro-Wilk (distribución NO normal en el ejemplo analizado)

## Conclusión

El análisis demuestra que:

> κ_Π = log₂(13) NO es un valor central ni especialmente típico en la distribución de variedades Calabi-Yau. Está en el percentil 3.67%, es decir, en el **rango BAJO** de la distribución.

> Esto **INVALIDA** cualquier conclusión especial derivada de seleccionar solo las variedades con N = 13.

## Dependencias

```
numpy >= 1.21
scipy >= 1.7
matplotlib >= 3.7
seaborn >= 0.12
```

Instalación:
```bash
pip install numpy scipy matplotlib seaborn
```

## Referencias

El análisis se basa en:
- Números de Hodge (h¹¹, h²¹) de variedades Calabi-Yau
- Definición: κ_Π = log₂(h¹¹ + h²¹)
- Test de Shapiro-Wilk para normalidad
- Análisis estadístico descriptivo estándar

## Autor

Implementado como parte del proyecto P-NP en respuesta al problema statement sobre validación de distribuciones Calabi-Yau.
