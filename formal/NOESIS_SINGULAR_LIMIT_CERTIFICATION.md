# 🌊 NOESIS — Certificación formal (ecosistema Lean)

**Fecha:** 2026-08-07  
**Módulo ancla:** `formal/SingularLimit.lean`  
**Integración:** importado en `formal/Formal.lean`

## Estado de certificación en el repositorio

Se incorporó una formalización estructurada del límite singular `ε → 0` con cuatro bloques:

1. **Convergencia de resolventes**  
   `step1_resolvent_strong`
2. **Convergencia de semigrupos (puente Trotter–Kato)**  
   `step2_semigroup_convergence`
3. **Cotas uniformes (`H¹` / enstrofía) y coherencia**  
   `step3_uniform_bounds`, `step3_coherence`
4. **Cierre espectral consolidado**  
   `spectralClosureTheorem`

Además, se añadió un certificado portable:

- `Certification`
- `certify`
- `certify_sound`

## Alcance matemático explícito

El cierre formal en Lean es **deductivo bajo hipótesis explícitas** (`SpectralClosureHypotheses` y `SingularLimitHypotheses`).  
Es decir, el módulo certifica:

- si se asume convergencia de resolventes,
- si se asume el puente de Trotter–Kato,
- si se asumen cotas uniformes y preservación de coherencia,

entonces se obtiene el cierre lógico conjunto del límite singular.

Esto deja el teorema **anclado al ecosistema formal del repositorio**, con dependencias y conclusiones trazables en código Lean.
