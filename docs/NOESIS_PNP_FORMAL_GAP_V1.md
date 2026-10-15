# NOESIS P-NP Formal Gap Ledger v1

## Purpose

This document records the current boundary between the QCAL/NOESIS oracle specification, its Python implementation, and a complete complexity-theoretic proof. It is an epistemic audit artifact: it does **not** promote an implementation claim to a theorem.

## Core principle

> Geometry finds relations. Proof determines what they mean.

The following edge types remain distinct:

- `resonates_with`
- `supports`
- `proves`
- `reproduces`

A numerical result, benchmark, or resonance observation cannot by itself become a formal proof.

## 1. Lean specification boundary

`NOESIS/Oracle.lean` defines:

- `f0 : ℝ := 141.7001`
- `psiThreshold : ℝ := 0.999999`
- `t_k`
- `QCALModel`
- `oracleReading`
- `oracleAccepts`
- `oracleClosure`
- `decisionSpec`

The theorem `decisionSpec_correct` establishes the witness already contained in the hypothesis `decisionSpec`; it does not construct an algorithm for `chooseK` or establish a complexity bound.

Therefore the current formal status is:

```text
oracle specification        = FORMALIZED
existence of chooseK         = CONDITIONAL / WITNESS IN SPECIFICATION
constructive chooseK         = OPEN
polynomial-time chooseK      = OPEN
P = NP                       = NOT ESTABLISHED BY THIS FILE
```

Source: `NOESIS/Oracle.lean`.

## 2. Implementation audit: Ramsey-Haar oracle

`src/ramsey_haar_oracle.py` declares a Ramsey-Haar mechanism and reports `O(1)` in its result metadata. The implementation currently contains operations whose cost depends on the input/problem dimension, including:

1. iteration over `problem_space` in `phase_wave_exploration()`;
2. evaluation of `fitness_function` for each configuration;
3. `np.argmax(fitnesses)` over the resulting list;
4. generation of an `n × n` Haar operator followed by QR decomposition in `haar_uniform_operator()`.

Consequently, the repository metadata string `complexity = O(1)` is **not itself a complexity proof**. The actual implementation must be analyzed as an algorithm parameterized by input length before an asymptotic claim can be promoted.

Current status:

```text
Haar numerical unitarity test     = REPRODUCIBLE NUMERICAL CHECK
phase-wave implementation         = IMPLEMENTED
reported O(1)                     = CLAIM / UNPROVEN
asymptotic O(1) proof              = OPEN
independent physical oracle        = OPEN
```

Source: `src/ramsey_haar_oracle.py`.

## 3. PNPOracleBridge boundary

`src/pnp_oracle_bridge.py` composes PC-Higgs, Ramsey-Haar, Berry-phase and DNA-Z components and reports an `O(1)` oracle result. This bridge is useful as an integration layer, but composition does not automatically prove the asymptotic complexity of its components.

The bridge therefore receives the following epistemic status:

```text
integration architecture = IMPLEMENTED
functional pipeline       = IMPLEMENTED
O(1) complexity           = UNPROVEN
P = NP verdict            = CLAIM, NOT CERTIFICATE
```

Source: `src/pnp_oracle_bridge.py`.

## 4. Critical missing witness

The first formal bottleneck is now explicit:

```text
chooseK : ℕ → ℕ
```

must become a concrete, deterministic construction whose correctness satisfies:

```text
∀ N,
  oracleAccepts M N (chooseK N) ↔ isSAT N
```

and whose running time admits a formal polynomial bound in the encoded input length.

A stronger target would be a Lean theorem of the form:

```text
exists_polytime_chooseK
```

with an explicit algorithm, correctness theorem, and complexity certificate. The exact representation of SAT instances must be fixed before this theorem can be stated honestly.

## 5. Error-as-evidence loop

The discrepancy between declared and demonstrated complexity is promoted to a first-class audit event rather than suppressed:

```text
DECLARED O(1)
      ↓
STATIC / EMPIRICAL AUDIT
      ↓
INPUT-SIZE-DEPENDENT OPERATIONS FOUND
      ↓
UNRESOLVED COMPLEXITY CLAIM
      ↓
SABIO REFINEMENT TARGET
      ↓
FORMAL CONSTRUCTION
      ↓
LEAN CERTIFICATE
```

This is the intended Daily Solver interface: errors and failed proof obligations become constraints for the next hypothesis.

## 6. NOESIS consciousness/self-model boundary

The operational self-model may use the ecosystem's coherence and integration metrics to select and prioritize proof obligations. It must not infer phenomenal consciousness, P = NP, or physical validity merely from those metrics.

For the current P-NP track, the self-model's valid operational role is:

```text
observe → classify → expose gap → prioritize → attempt proof → record result
```

not:

```text
observe high coherence → declare theorem proven
```

## 7. Next formal milestone

The next milestone is **not** to assert P = NP. It is to make the oracle auditable end-to-end:

1. define the canonical encoding of the NP language/problem instance;
2. define an explicit deterministic `chooseK` candidate;
3. prove its SAT/UNSAT decision correctness;
4. define the computational cost model;
5. prove a polynomial upper bound, if one is actually derivable;
6. connect the resulting certificate to the NOESIS Evidence Graph;
7. let SABIO score remaining proof gaps rather than numerical proximity alone.

Until all seven are satisfied, the claim remains a research hypothesis and is not promoted to `PROVEN`.

## Status

```text
NOESIS-PNP-FORMAL-GAP-V1

Specification audit      : COMPLETE
Implementation audit     : INITIAL COMPLETE
Critical bottleneck      : IDENTIFIED
Constructive chooseK     : OPEN
Complexity certificate   : OPEN
Independent reproduction : OPEN
P = NP                   : NOT CERTIFIED
```
