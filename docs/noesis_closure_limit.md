# NOESIS / QCAL-DCM — Cierre formal del límite de evaluación polinómica

Este documento ancla en el repositorio la síntesis acordada en el análisis:

1. La evaluación del observable \(\Psi(T^\*)\) tiene dos regímenes:
   - **Exacto** (sin truncamiento): preserva la señal decisoria, pero puede requerir dimensión no polinómica.
   - **Reducido polinómico** (truncamiento/proyección): ejecutable en tiempo polinómico, con riesgo de pérdida de información espectral en el peor caso.
2. Para conectar con complejidad de clases, se formaliza una implicación **condicional**:
   - Si existe evaluación polinómica exacta uniforme que preserva el criterio SAT/UNSAT para toda instancia, entonces existe un decisor polinómico en ese marco.
   - Cualquier afirmación global de tipo `P = NP` o `P ≠ NP` requiere hipótesis adicionales explícitas.

## Archivo Lean anclado

- `/home/runner/work/P-NP/P-NP/NOESIS/ClosureLimit.lean`

Contenido formalizado:

- `SpectralModel`: interfaz abstracta del modelo espectral.
- `exactDecisionSpec`: especificación de correctitud del observable exacto.
- `uniformPolynomialExactness`: exactitud uniforme de una evaluación polinómica truncada.
- `hasPolynomialDecider`: noción abstracta de decisor polinómico en el marco del observable.
- `uniform_exactness_gives_decider`: teorema constructivo principal.
- `conditional_P_eq_NP_from_uniform_exactness`: forma condicional hacia clases de complejidad.
- `no_decider_implies_no_uniform_exactness`: contraposición formal.

## Nota de rigor

La formalización evita declarar como teoremas incondicionales resultados abiertos de complejidad.
En su lugar, deja explícitas las dependencias lógicas entre:

- exactitud de evaluación,
- validez del criterio de decisión,
- y consecuencias de complejidad.
