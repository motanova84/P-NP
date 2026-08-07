# QCAL-Adelic Operational Formalization

## Anchors
- \(f_0 = 141.7001\,\text{Hz}\)
- \(\omega_0 = 2\pi f_0\)
- \(\Psi^\* = 0.999999\)

## Critical clock
For \(N>1\):
\[
t_k = \frac{k}{f_0}\ln(N),\quad k\in\mathbb{N}_{>0}
\]

## Coherence envelope
\[
\Psi(N,t)=\exp\left(-\left(\frac{\omega_0(t-t_k)}{b}\right)^2\right),
\]
using nearest \(t_k\) and bandwidth \(b>0\), clipped at \(\Psi^\*\).

## Operational factorization
1. Iterate \(d=2,\dots,\lfloor\sqrt N\rfloor\).
2. Compute arithmetic-resonance score \(S_d\in[0,\Psi^\*]\), with max value on exact divisors.
3. Keep best exact divisor pair \((d, N/d)\).
4. Verify \(d\mid N\), \(1<d<N\), \(1<N/d<N\).

## Implemented artifacts
- Module: `/home/runner/work/P-NP/P-NP/qcal_adelic_operational.py`
- CLI: `/home/runner/work/P-NP/P-NP/scripts/run_qcal_adelic_operational.py`
- Tests: `/home/runner/work/P-NP/P-NP/tests/test_qcal_adelic_operational.py`

## Usage
```bash
python3 /home/runner/work/P-NP/P-NP/scripts/run_qcal_adelic_operational.py 77 --k-max 5
```

Returns anchors, critical times, coherence trace and verified factorization payload.
