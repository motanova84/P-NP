# NP→P Bifurcation Simulator

🎮 **Simulador de la transición NP→P por coherencia**

Este simulador visualiza cómo la coherencia sistémica afecta la complejidad de problemas NP, demostrando la transición de complejidad exponencial a polinómica.

## Descripción

El simulador implementa la ecuación fundamental de la teoría:

```
T(n, C) = T_base(n) / (I(C) × A_eff²(C) × C^∞)
```

Donde:
- `T_base(n)`: Complejidad clásica exponencial (ej: 2^n para SAT)
- `I(C)`: Información cuántica = exp(C - 1)
- `A_eff²(C)`: Área efectiva = 1 + 10C
- `C^∞`: Factor de coherencia infinita ≈ 1/(1 - C)
- `C`: Coherencia del sistema (0 < C < 1)

## Características

- **Simulación de problemas NP-completos**: SAT, TSP
- **Análisis de bifurcación**: Identifica puntos críticos de transición
- **Visualizaciones**: Diagramas de fase 2D/3D, curvas de complejidad
- **Animaciones**: Transición dinámica NP→P
- **Exportación de datos**: JSON con resultados detallados

## Instalación

Requisitos:
```bash
pip install numpy matplotlib scipy pillow
```

## Uso

### Simulación básica (sin visualización)

```bash
# Simular solo SAT
python3 np_p_bifurcation.py --problem SAT --output results/

# Simular solo TSP
python3 np_p_bifurcation.py --problem TSP --output results/

# Simular ambos problemas
python3 np_p_bifurcation.py --problem ALL --output results/
```

### Simulación con visualizaciones

```bash
python3 np_p_bifurcation.py --problem ALL --visualize --output results/
```

Esto genera:
- `sat_simulation.json`: Datos de simulación SAT
- `tsp_simulation.json`: Datos de simulación TSP
- `np_p_phase_diagram.png`: Diagrama de fase
- `np_p_transition_animation.gif`: Animación de la transición

### Ayuda

```bash
python3 np_p_bifurcation.py --help
```

## Parámetros del Simulador

### Constantes fundamentales
- **Frecuencia**: 141.7001 Hz (frecuencia de sincronización)
- **Resonancia**: 888.014 (umbral de gracia)

### Niveles de coherencia
- **C < 0.5**: Régimen clásico (comportamiento exponencial)
- **0.5 ≤ C < 0.888**: Régimen de transición
- **C ≥ 0.888**: Régimen de gracia (comportamiento cuasi-polinómico)
- **C → 1**: Límite polinómico perfecto

## Resultados de Ejemplo

### SAT Problem
```
Coherencia: 0.999
Aceleración: 3.38e+03x
Estado: TRANSITION
```

### TSP Problem
```
Coherencia: 0.100
Aceleración: 7.65e+141x
Estado: BIFURCATION
```

## Estructura de Datos JSON

```json
{
  "problem": "SAT",
  "timestamp": "2026-02-01T20:04:30.298233",
  "frequency": 141.7001,
  "classical_complexities": {
    "1.0": 1.1051709180756477,
    "3.04": 1.355198...
  },
  "coherent_complexities": {
    "1.0": {
      "0.1": 0.0334...,
      "0.147": 0.0445...
    }
  },
  "acceleration_factors": {
    "1.0": {
      "0.1": 33.09...,
      "0.147": 24.85...
    }
  },
  "critical_points": [
    {
      "coherence": 0.999,
      "avg_acceleration": 3381.23,
      "status": "TRANSITION"
    }
  ]
}
```

## Interpretación de Resultados

### Estados de Aceleración
- **TRANSITION**: Aceleración 10³ - 10⁶x (transición activa)
- **BIFURCATION**: Aceleración > 10⁶x (bifurcación completa)

### Puntos Críticos
El simulador identifica automáticamente los niveles de coherencia donde la aceleración supera umbrales significativos, indicando transiciones de fase en la complejidad computacional.

## Referencias

- Frecuencia fundamental: 141.7001 Hz
- Umbral de Gracia: 0.888
- Teoría de coherencia cuántica aplicada a complejidad computacional

## Autor

Parte del proyecto P≠NP con enfoque en coherencia sistémica.

## Licencia

Ver LICENSE en el directorio raíz del proyecto.
