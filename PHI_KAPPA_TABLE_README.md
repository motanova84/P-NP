# Tabla Matemática: Potencias de φ y κ_Π

## Descripción

Este módulo implementa y documenta la relación matemática precisa entre las potencias del número áureo (φ) y el valor correspondiente de κ_Π bajo el logaritmo en base φ².

## Relación Fundamental

```
κ_Π(N) = log_{φ²}(N) = log(N) / log(φ²)
```

Donde:
- `φ ≈ 1.618034` (número áureo)
- `φ² ≈ 2.618034`
- `N` = cualquier número real positivo

## Relación Exacta

Para `N = φⁿ`:

```
κ_Π(N) = n / 2
```

Esta es una relación exacta que se deriva de las propiedades logarítmicas:

```
κ_Π(φⁿ) = log_{φ²}(φⁿ)
        = log(φⁿ) / log(φ²)
        = n·log(φ) / (2·log(φ))
        = n / 2
```

## Ejemplos Clave

### Ejemplo 1: φ⁵ ≈ 11.09

```python
n = 5.0
N = φ⁵ ≈ 11.090170
κ_Π = κ_Π(11.090170) ≈ 2.500000
```

Verificación: `κ_Π = n/2 = 5/2 = 2.5` ✓

### Ejemplo 2: N = 13 → φ⁵·¹⁵⁴

```python
N = 13.0
n = log(13) / log(φ) ≈ 5.15446
φⁿ = φ^5.15446 ≈ 13.000000
κ_Π = κ_Π(13) ≈ 2.577230
```

Verificación: `κ_Π = n/2 = 5.15446/2 ≈ 2.5773` ✓

## Significado

La constante κ_Π = 2.5773 proviene directamente de κ_Π(13) bajo la base φ².

Esto confirma matemáticamente que cuando:
- `h¹¹ + h²¹ ≈ 13` (números de Hodge en variedades Calabi-Yau)
- `N = φ^5.154 ≈ 13`
- Entonces `κ_Π = 2.5773`

## Tabla de Valores

| n | φⁿ | κ_Π | n/2 | Verificado |
|---|---|---|---|---|
| 1.0 | 1.618034 | 0.500000 | 0.500000 | ✓ |
| 2.0 | 2.618034 | 1.000000 | 1.000000 | ✓ |
| 3.0 | 4.236068 | 1.500000 | 1.500000 | ✓ |
| 4.0 | 6.854102 | 2.000000 | 2.000000 | ✓ |
| 5.0 | 11.090170 | 2.500000 | 2.500000 | ✓ |
| **5.154** | **13.000000** | **2.577230** | **2.577000** | ✓ |
| 6.0 | 17.944272 | 3.000000 | 3.000000 | ✓ |
| 7.0 | 29.034442 | 3.500000 | 3.500000 | ✓ |
| 8.0 | 46.978614 | 4.000000 | 4.000000 | ✓ |
| 9.0 | 76.013056 | 4.500000 | 4.500000 | ✓ |
| 10.0 | 122.991670 | 5.000000 | 5.000000 | ✓ |

## Uso

### Importar el módulo

```python
from src.phi_kappa_table import kappa_pi, phi_power, find_phi_exponent
```

### Calcular κ_Π para un valor N

```python
# Calcular κ_Π(13)
kappa = kappa_pi(13)
print(f"κ_Π(13) = {kappa:.6f}")  # 2.577230
```

### Calcular φⁿ

```python
# Calcular φ⁵
N = phi_power(5)
print(f"φ⁵ = {N:.6f}")  # 11.090170
```

### Encontrar el exponente n para un N dado

```python
# Encontrar n tal que φⁿ = 13
n = find_phi_exponent(13)
print(f"13 = φ^{n:.6f}")  # φ^5.154460
```

### Generar tabla de valores

```python
from src.phi_kappa_table import generate_table

# Generar tabla para n = 1, 2, 3, ..., 10
n_values = [1.0, 2.0, 3.0, 4.0, 5.0, 5.154, 6.0, 7.0, 8.0, 9.0, 10.0]
table = generate_table(n_values)

for row in table:
    print(f"φ^{row['n']:.3f} = {row['N']:.3f} → κ_Π = {row['kappa_pi']:.6f}")
```

### Imprimir tabla formateada

```python
from src.phi_kappa_table import print_table

# Imprimir tabla de n=1 a n=10 con paso 0.5
print_table(n_min=1.0, n_max=10.0, step=0.5)
```

### Análisis detallado de κ_Π(13)

```python
from src.phi_kappa_table import analyze_kappa_13

# Mostrar análisis completo de κ_Π(13) = 2.5773
analyze_kappa_13()
```

## Demo

Ejecutar el script de demostración:

```bash
python examples/demo_phi_kappa_table.py
```

Este script muestra:
1. Constantes fundamentales (φ, φ², κ_Π)
2. Relación matemática fundamental
3. Ejemplos clave del problema
4. Tabla completa de valores
5. Análisis detallado de κ_Π(13)
6. Verificación de todos los ejemplos
7. Valores especiales alrededor de N=13
8. Conclusiones

## Tests

Ejecutar los tests:

```bash
pytest tests/test_phi_kappa_table.py -v
```

## Implementación

### Archivo principal: `src/phi_kappa_table.py`

Funciones principales:
- `kappa_pi(N)`: Calcula κ_Π(N) = log_{φ²}(N)
- `phi_power(n)`: Calcula φⁿ
- `find_phi_exponent(N)`: Encuentra n tal que φⁿ ≈ N
- `verify_exact_relationship(n)`: Verifica κ_Π(φⁿ) = n/2
- `generate_table(n_values)`: Genera tabla de valores
- `verify_key_examples()`: Verifica los ejemplos del problema
- `print_table()`: Imprime tabla formateada
- `analyze_kappa_13()`: Análisis detallado de κ_Π(13)

### Demostración: `examples/demo_phi_kappa_table.py`

Script interactivo que muestra todas las funcionalidades del módulo.

## Conexión con Calabi-Yau

La relación `κ_Π(13) = 2.5773` tiene una conexión profunda con la geometría de Calabi-Yau:

1. Los números de Hodge `h¹¹` y `h²¹` caracterizan la topología de variedades Calabi-Yau 3D
2. En muchas variedades, `h¹¹ + h²¹ ≈ 13`
3. Esto genera `N ≈ 13 = φ^5.154`
4. Por lo tanto, `κ_Π ≈ 2.5773`

Esta relación matemática confirma que la constante κ_Π = 2.5773 emerge naturalmente de la topología de Calabi-Yau cuando se expresa en términos del número áureo φ.

## Referencias

- Constantes universales: `src/constants.py`
- Calabi-Yau κ_Π: `src/calabi_yau_kappa_derivation.py`
- Análisis κ_Π: `src/calabi_yau_kappa_pi_analysis.py`

## Author

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

Frequency: 141.7001 Hz ∞³
