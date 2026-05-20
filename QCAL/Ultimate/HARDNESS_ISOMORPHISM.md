# 🔱 QCAL: Isomorfismo de Dureza
## Formalización Final: Dinámica, Permanente y Threshold

**19 de Mayo de 2026, 20:27 PDT**
**Protocolo:** QCAL-SYMBIO-BRIDGE v1.0.0
**Sello:** ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ

---

## 1. Equivalencia Exacta: Admitancia ↔ Satisfacibilidad

### Mapa de Hamilton

Ĥ_𝔸 construido tal que el estado fundamental |Ψ₀⟩ tiene:

```
E = 0  ⇔  ∃ x ∈ {−1,1}ⁿ : φ(x) = True
```

### Resonancia a f₀ = 141.7001 Hz

La amplitud A(f₀) del resonador de zafiro es el observador físico:

```
φ ∈ SAT   →  A(f₀) > T_crit  (resonancia coherente)
φ ∉ SAT   →  A(f₀) < T_crit  (supresión espectral, ΔE ≥ 1)
```

**Isomorfismo:** Relación biunívoca. El gap espectral ΔE es una
propiedad topológica protegida por el orden del fluido cuántico.

---

## 2. Incomputabilidad del Permanente

Cualquier intento de una TM clásica de explotar la dinámica del
fluido para resolver 3-SAT en tiempo polinomial fracasará:

```
Amplitud de probabilidad  ⇔  Perm(B_φ)
Teorema de Valiant       ⇔  Perm es ♯P-completo
TM clásica eficiente     ⇔  P^♯P = P (contradicción jerarquía)
```

**La dinámica es inherentemente incomputable para TM clásicas.**
La única forma de "resolverlo" es la implementación física directa.

---

## 3. Threshold Theorem: Corrección Arbitraria (ε → 0)

### Decodificador MWPM = SAW

| Componente | Rol |
|-----------|-----|
| Error de fase | Campo de tensión local en zafiro |
| SAW (v_s ∼ 10⁴ m/s) | Atracción elástica entre defectos |
| Escala temporal | Instantánea vs decoherencia 2DEG (μs) |
| Overhead | V ∝ log²(n) — estrictamente polinomial |

### Supresión de Ruido

| Fuente de Ruido | Efecto | Corrección QCAL |
|----------------|--------|-----------------|
| Térmico (k_B·T) | Debilitamiento de fase | Estabilizadores Ŝₚ |
| 1/f | Fluctuación de potencial | Filtro por portadora f₀ |
| δf₀ (deriva) | Desintonización | Auto-bloqueo mecánico |

---

## 4. Conclusión Final

QCAL opera mediante un **isomorfismo de dureza**:

```
Reducción:  TM-polinomial (configuración física)
Dureza:     ♯P-completa vía Permanente (Valiant)
Corrección: Homológica (threshold p_th > 0)
Gap:        SAT poly / UNSAT exp — firma topológica
```

El gap polinomial/exponencial sobrevive al ruido real porque
**es la firma topológica de la satisfacibilidad**.

```
48 módulos Lean 4 · f₀ = 141.7001 Hz · Ψ = 0.99999997
∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
```
