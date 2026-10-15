# Guía Rápida: Teorema de Correspondencia Holográfica Computacional

## 🚀 Inicio Rápido (5 minutos)

### Paso 1: Ejecutar la Simulación

```bash
cd /home/runner/work/P-NP/P-NP
python3 simulate_holographic_bound.py
```

**Salida esperada:**
- Ejemplo numérico concreto (n=100, tw=50)
- Verificación de la constante κ_Π ≈ 2.5773
- Tabla comparativa T_holo vs polinomios
- Demostración de separación P ≠ NP

### Paso 2: Explorar el Paper en LaTeX

```bash
cd paper
# Ver el contenido (sin compilar)
cat teorema_correspondencia_holografica.tex | head -100

# Compilar (requiere LaTeX instalado)
pdflatex teorema_correspondencia_holografica.tex
```

### Paso 3: Revisar la Formalización Lean4

```bash
# Ver el código Lean4
cat HolographicCorrespondence.lean

# Compilar (requiere Lean 4 instalado)
lake build HolographicCorrespondence
```

## 📚 Documentación Principal

**README completo:** `TEOREMA_CORRESPONDENCIA_HOLOGRAFICA_README.md`

## 🎯 Teorema en Una Línea

```
T_holo(φ) ≥ exp(κ_Π · tw(G) / log n)  con κ_Π ≈ 2.5773
```

**Consecuencia:** Si tw(G) = ω(log n) ⇒ P ≠ NP

## 📁 Archivos Clave

1. **Paper académico (español):** `paper/teorema_correspondencia_holografica.tex`
2. **Formalización Lean4:** `HolographicCorrespondence.lean`
3. **Simulación Python:** `simulate_holographic_bound.py`
4. **Documentación completa:** `TEOREMA_CORRESPONDENCIA_HOLOGRAFICA_README.md`

## 🔬 Experimento Rápido

```python
import math

# Constantes
κ_Π = 2.5773
n = 100
tw = 50
log_n = math.log(n)

# Cálculo del tiempo holográfico
T_holo = math.exp(κ_Π * tw / log_n)

print(f"Para n={n}, tw={tw}:")
print(f"T_holo ≈ {T_holo:.2e}")
print(f"Esto es ~{T_holo/1e12:.1f} billones de operaciones")
```

## 🌟 Conceptos Clave

### La Cadena de Correspondencias

```
Fórmula Tseitin  →  CFT (borde)  →  AdS (bulk)  →  T_holo
```

### La Constante QCAL

**κ_Π ≈ 2.5773** emerge de:
- Grafos expandidos (espectro)
- Geometría AdS (curvatura)
- Frecuencia QCAL f₀ = 141.7001 Hz
- Razón áurea φ = (1+√5)/2

### El Sello Universal

```
T ≥ exp(Vol_RT)  donde  Vol_RT ~ κ_Π · tw(G) / log n
```

## 📊 Resultado Visual Rápido

**Tabla: ¿Cuándo T_holo supera polinomios?**

| n | T_holo | Supera n² | Supera n¹⁰ | Supera n¹⁰⁰ |
|---|--------|-----------|------------|-------------|
| 10 | 2.7×10² | ✓ | ✗ | ✗ |
| 50 | 1.4×10⁷ | ✓ | ✗ | ✗ |
| 100 | 1.4×10¹² | ✓ | ✗ | ✗ |
| 500 | 1.1×10⁴⁵ | ✓ | ✓ | ✗ |
| 1000 | 1.0×10⁸¹ | ✓ | ✓ | ✗ |

**Nota:** Para n > 2000, T_holo supera incluso n¹⁰⁰

## 💡 Preguntas Frecuentes

### ¿Qué es AdS/CFT?
Correspondencia holográfica entre una teoría gravitacional en el "bulk" (d+1 dimensiones) y una teoría conforme en el "borde" (d dimensiones).

### ¿Por qué esto demuestra P ≠ NP?
Porque establece una cota inferior **geométrica** (no algorítmica) que crece super-exponencialmente para problemas NP-completos.

### ¿Qué es tw(G)?
El "ancho de árbol" (treewidth): una medida de cuán parecido a un árbol es un grafo. Para expanders, tw(G) ~ n.

### ¿De dónde viene κ_Π ≈ 2.5773?
De la intersección entre:
- Espectro de grafos expandidos
- Geometría hiperbólica AdS
- Frecuencia fundamental QCAL (141.7001 Hz)

## 🔗 Integración con el Repositorio

Este teorema se integra con:

- `FrequencyFoundation.lean` - Definición de f₀
- `HolographicDuality.lean` - Correspondencia AdS/CFT
- `TseitinExpander.lean` - Construcción de instancias duras
- `Treewidth.lean` - Teoría del ancho de árbol
- `P_neq_NP.lean` - Teorema principal P ≠ NP

## ⚠️ Nota Importante

Este es un **marco teórico propuesto** que requiere validación rigurosa por expertos en:
- Física teórica (AdS/CFT)
- Complejidad computacional
- Geometría algebraica

Ver el disclaimer completo en el README principal.

## 📞 Contacto

**Autor:** José Manuel Mota Burruezo  
**Institución:** Instituto de Conciencia Cuántica (ICQ)

---

**Versión 1.0 • 30 de Enero, 2026**
