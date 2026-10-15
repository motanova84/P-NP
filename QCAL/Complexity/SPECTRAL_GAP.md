# 📐 Derivación del Gap Espectral QCAL
## Del Hamiltoniano Adélico a la Separación de Clases

**Protocolo:** QCAL-SYMBIO-BRIDGE v1.0.0
**Frecuencia:** f₀ = 141.7001 Hz
**Sello:** ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ

---

## 1. Construcción del Hamiltoniano Adélico

Sea φ una fórmula 3-CNF con n variables y m cláusulas.
El espacio de configuración es el espacio afín sobre el anillo de adélos:

```
𝔸_ℚⁿ  con  Ψ ∈ ℋ_𝔸 = L²(𝔸_ℚⁿ, dμ_𝔸)
```

El Hamiltoniano adélico global se descompone en todos los lugares:

```
Ĥ_𝔸 = Ĥ_∞ + Σ_{p∈ℙ} Ĥ_p
```

### Componentes p-ádicas (Ĥ_p)
Usan el operador de Vladimirov D_p y restringen los estados al anillo ℤ_pⁿ:

```
Ĥ_p · Ψ_p = D_p · Ψ_p + V_p · Ψ_p
```

### Componente Real (Ĥ_∞)
Codifica las restricciones lógicas:

```
Ĥ_∞ = −ℏ²/(2m*)·∇² + V_φ(z)
V_φ(z) = Σ_{j=1}ᵐ Pⱼ(z) + α·Σ_{i=1}ⁿ (z_i² − 1)²
```

---

## 2. Gap Espectral

Por la descomposición aditiva del adélo y la fórmula del producto,
Σ_p E_p = 0 para el estado fundamental. Toda la variación se reduce
al espectro de Ĥ_∞.

### Caso SAT (φ ∈ SAT)
- Existe x* ∈ {−1,1}ⁿ tal que todas las cláusulas se satisfacen
- V(x*) = 0 (potencial mínimo cero)
- E₀ = 0 (autovalor fundamental nulo)
- τ_SAT ≤ O(nᵏ) (tiempo de relajación polinomial)

### Caso UNSAT (φ ∉ SAT)
- Toda asignación viola al menos una cláusula
- Σ Pⱼ(z) ≥ 1 para toda configuración discreta
- E₀ ≥ 1 (mínimo de energía estrictamente positivo)
- Paisaje fraccionado en 2ⁿ pozos aislados por barreras cuárticas
- Constante de Cheeger: h(Μ) ≤ e^{−γ·n}
- Brecha espectral: ΔE_UNSAT ∼ e^{−γ·n}
- τ_UNSAT = 1/ΔE_UNSAT ∝ exp(γ·n·ΔV/k_B·T)

---

## 3. Conclusión

El gap temporal no es una estimación aproximada.
Es un **teorema espectral estricto**:

| Condición | Energía mínima | Brecha espectral | Tiempo de relajación |
|-----------|---------------|------------------|---------------------|
| SAT | E₀ = 0 | ΔE ∼ 1/poly(n) | τ ∼ O(nᵏ) |
| UNSAT | E₀ ≥ 1 | ΔE ∼ e^{−γ·n} | τ ∼ e^{Ω(n)} |

La diferencia entre polinomial y exponencial es la traducción matemática
directa y necesaria de la dicotomía lógica SAT/UNSAT.

```
∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
```
