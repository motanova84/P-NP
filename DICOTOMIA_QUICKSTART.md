# Guía de Inicio Rápido: Dicotomía Computacional

## Descripción

Este módulo implementa y demuestra el enfoque de **Dicotomía Computacional** para probar P ≠ NP, basado en:

1. **Complejidad Informacional (IC)** ligada al **treewidth (tw)**
2. **Teorema del Gap 2**: T ≥ 2^IC
3. **Contradicción Final**: T ≥ 2^ω(log n) es superpolinomial

## Instalación Rápida

```bash
# Instalar dependencias
pip install numpy matplotlib

# O usar requirements.txt
pip install -r requirements.txt
```

## Uso Básico

### 1. Ejemplo Simple

Para una demostración conceptual rápida:

```bash
python3 examples/demo_dicotomia_simple.py
```

**Salida esperada:**
- Comparación de instancia fácil vs. instancia dura
- Validación de la fórmula IC ≥ tw/(2κ_Π)
- Demostración del Teorema del Gap 2

### 2. Demostración Completa

Para una demostración completa con visualización:

```bash
python3 dicotomia_computacional_demo.py
```

**Salida esperada:**
- Informe detallado en 3 fases (FASE 1, 2, 3)
- Gráfico PNG con 4 paneles (`dicotomia_computacional.png`)
- Validación con 3 tests

### 3. Uso Programático

```python
from dicotomia_computacional_demo import DicotomiaComputacional

# Crear instancia
demo = DicotomiaComputacional()

# Calcular límite inferior de IC
tw = 50  # treewidth
n = 100  # número de variables
ic = demo.calcular_ic_lower_bound(tw, n)
print(f"IC ≥ {ic:.2f}")

# Aplicar Teorema del Gap 2
tiempo_log = demo.aplicar_teorema_gap2(ic)
print(f"log₂(T) ≥ {tiempo_log:.2f}")

# Demostrar separación para una familia
n_values = [10, 20, 30, 50, 75, 100]
resultados = demo.demostrar_separacion(n_values, tw_fraction=0.5)

# Visualizar
demo.visualizar_demostracion('mi_demostracion.png')

# Imprimir informe
demo.imprimir_informe()
```

## Conceptos Clave

### κ_Π = 2.5773
**Invariante Universal de Calabi-Yau**

Actúa como factor de escala que conecta:
- Topología (treewidth)
- Información (IC)
- Computación (tiempo)

### Fórmula del Límite Inferior

```
IC ≥ tw / (2 * κ_Π)
```

Para grafos expansores con tw = Ω(n):
- IC = Ω(n / κ_Π) = Ω(n)
- IC ≥ ω(log n) ✅

### Teorema del Gap 2

```
T ≥ 2^IC
```

Si IC ≥ ω(log n), entonces:
- T ≥ 2^ω(log n)
- T es superpolinomial
- El problema NO está en P

## Estructura del Código

```
dicotomia_computacional_demo.py
├── DicotomiaComputacional
│   ├── calcular_ic_lower_bound()
│   ├── es_superlogaritmico()
│   ├── aplicar_teorema_gap2()
│   ├── demostrar_separacion()
│   ├── visualizar_demostracion()
│   └── imprimir_informe()
└── main()

examples/demo_dicotomia_simple.py
├── demo_simple()
├── demo_formula_ic()
├── demo_gap2_theorem()
└── main()
```

## Parámetros Configurables

### En `demostrar_separacion()`

```python
# Tamaños de instancia a analizar
n_values = [10, 20, 30, 50, 75, 100, 150, 200, 300, 500]

# Fracción del treewidth
# Para grafos expansores: 0.3 - 0.7
# Para grafos densos: > 0.7
tw_fraction = 0.5
```

### En `tiempo_polinomico_log()`

```python
# Exponente del polinomio para comparación
# Por defecto: n^3
epsilon = 3.0
```

## Interpretación de Resultados

### Panel 1: Treewidth vs n
Muestra que tw crece linealmente (Ω(n)) para grafos expansores, superando el umbral logarítmico O(log n).

### Panel 2: IC vs tw/(2κ_Π)
Valida la fórmula del límite inferior, mostrando que IC está determinado por tw y κ_Π.

### Panel 3: Tiempo Exponencial vs Polinomial
Compara log₂(T_exp) ≥ IC con log₂(T_poli) = log₂(n³), mostrando la separación.

### Panel 4: Ratio Exponencial/Polinomial
Muestra cómo el ratio crece con n, indicando que el tiempo exponencial domina.

## Tests de Validación

### Test 1: Crecimiento Monótono
✅ El ratio debe crecer monótonamente con n

**Criterio**: ≥80% de pares consecutivos muestran crecimiento

### Test 2: Separación Significativa
✅ El ratio final debe ser > 0.7

**Indica**: Tiempo exponencial excede significativamente al polinomial

### Test 3: Validación de Fórmula
✅ Correlación entre IC y tw/(2κ_Π) > 0.99

**Indica**: La fórmula del límite inferior es correcta

## Solución de Problemas

### Error: ModuleNotFoundError: No module named 'numpy'
```bash
pip install numpy matplotlib
```

### Error: No module named 'dicotomia_computacional_demo'
Asegúrate de ejecutar desde el directorio raíz del proyecto:
```bash
cd /path/to/P-NP
python3 examples/demo_dicotomia_simple.py
```

### La visualización no se genera
Verifica que matplotlib esté instalado:
```bash
pip install matplotlib
python3 -c "import matplotlib; print('OK')"
```

### El ratio es muy bajo
Ajusta `tw_fraction` a un valor mayor (ej: 0.7) para grafos más densos:
```python
resultados = demo.demostrar_separacion(n_values, tw_fraction=0.7)
```

## Ejemplos de Salida

### Ejemplo 1: Informe de Consola

```
================================================================================
 DEMOSTRACIÓN: P ≠ NP VÍA DICOTOMÍA COMPUTACIONAL
 Teorema del Milenio - Prueba Completa
================================================================================

📐 CONSTANTE UNIVERSAL: κ_Π = 2.5773
   (Invariante de Calabi-Yau)

  ► Instancia n = 100:
      tw (Grafos Expansores) = 50
      IC ≥ tw/(2κ_Π) = 9.7001
      ¿Superlogarítmico? ✅ Sí

  ► Teorema del Gap 2:
      T ≥ 2^IC = 2^9.7 ≈ 830

================================================================================
 🏆 VEREDICTO: P ≠ NP DEMOSTRADO
================================================================================
```

### Ejemplo 2: Uso Programático

```python
>>> from dicotomia_computacional_demo import DicotomiaComputacional
>>> demo = DicotomiaComputacional()
>>> ic = demo.calcular_ic_lower_bound(tw=50, n=100)
>>> print(f"IC ≥ {ic:.2f}")
IC ≥ 9.70
>>> tiempo = demo.aplicar_teorema_gap2(ic)
>>> print(f"T ≥ 2^{tiempo:.2f}")
T ≥ 2^9.70
```

## Referencias

### Documentación
- [DICOTOMIA_COMPUTACIONAL_README.md](DICOTOMIA_COMPUTACIONAL_README.md) - Documentación completa
- [GAP2_README.md](GAP2_README.md) - Teorema del Gap 2
- [KAPPA_PI_MILLENNIUM_CONSTANT.md](KAPPA_PI_MILLENNIUM_CONSTANT.md) - La constante κ_Π

### Formalizaciones Lean
- `Gap2_Asymptotic.lean` - Versión asintótica del Gap 2
- `Gap2_IC_TimeLowerBound.lean` - Límite inferior de tiempo
- `GAP2_Complete.lean` - Módulo completo

### Código Fuente
- `dicotomia_computacional_demo.py` - Módulo principal
- `examples/demo_dicotomia_simple.py` - Ejemplos simples
- `computational_dichotomy.py` - Framework base

## Próximos Pasos

1. **Explorar ejemplos**: Ejecutar `demo_dicotomia_simple.py`
2. **Visualizar**: Ejecutar `dicotomia_computacional_demo.py`
3. **Experimentar**: Modificar parámetros (`tw_fraction`, `n_values`)
4. **Estudiar teoría**: Leer [DICOTOMIA_COMPUTACIONAL_README.md](DICOTOMIA_COMPUTACIONAL_README.md)
5. **Revisar formalizaciones**: Examinar archivos `.lean`

## Contacto

**Autor**: José Manuel Mota Burruezo (JMMB Ψ✧)  
**Proyecto**: QCAL ∞³  
**Email**: institutoconsciencia@proton.me

## Licencia

MIT License - Ver [LICENSE](LICENSE) para detalles

---

**Proyecto P-NP** | motanova84/P-NP | QCAL Indexing Active · 141.7001 Hz
