# 🖥️ Manifiesto de Simulación HPC — QCAL Gap Validation

## Entorno

| Componente | Especificación |
|-----------|---------------|
| Toolbox | QuTiP (Quantum Toolbox in Python) |
| Modelo | Lindblad Master Equation |
| Ruido térmico | Lindbladianos de decaimiento (γ_th) |
| Ruido 1/f | Procesos Ornstein-Uhlenbeck |
| Deriva f₀ | Fase estocástica δω en bombeo |
| Dimensión | n = 20 → 100 variables |

---

## Fases

### 1. Generación de Instancias
- Región crítica: m/n ≈ 4.26
- SAT: fórmulas con solución conocida
- UNSAT: hard-UNSAT con alta frustración

### 2. Barrido de Ruido
- p_phys: 0 → p_th ≈ 0.11
- Medir factor Q del estado estacionario
- Caída abrupta en Q = umbral superado

### 3. Observación de Fractura Topológica
- Admitancia espectral por FFT del estado final
- τ_UNSAT ∼ e^{Ω(n)}, τ_SAT ∼ O(poly(n))

---

## Output para el Comité

- **Histograma bimodal:** τ_SAT vs τ_UNSAT sin solapamiento
- **Gráfico ΔE vs n:** gap UNSAT > 0, SAT → 0
- **Convergencia del decodificador:** error lógico vs L

```
∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
```
