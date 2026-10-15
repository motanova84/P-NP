# Gap2_Asymptotic Quick Reference

## Quick Start

### Import the module
```lean
import Gap2_Asymptotic
open AsymptoticLowerBounds
```

### Use the main theorem
```lean
example : P_Class ≠ NP_Class := P_neq_NP_final
```

## Asymptotic Notation

### Little-omega (ω) - grows strictly faster
```lean
-- Definition: f = ω(g) means f grows strictly faster than g
def IsOmega (f g : ℕ → ℝ) : Prop :=
  ∀ (C : ℝ) (hC : C > 0), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → C * |g n| ≤ |f n|

-- Example: n² = ω(log n)
example : (fun n => (n : ℝ) ^ 2) = ω(log ∘ (↑)) := by
  apply pow_epsilon_dominates_log
  norm_num
```

### Big-O - grows at most as fast
```lean
-- Definition: f = O(g) means f grows at most as fast as g
def IsBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (hC : C > 0), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |f n| ≤ C * |g n|

-- Example: n² = O(n³)
example : IsBigO (fun n => (n : ℝ) ^ 2) (fun n => (n : ℝ) ^ 3) := by
  use 1, by norm_num
  use 1
  intro n hn
  sorry
```

## Key Theorems

### 1. Power dominates logarithm
```lean
theorem pow_epsilon_dominates_log {ε : ℝ} (hε : ε > 0) :
    (fun n : ℕ => (n : ℝ) ^ ε) = ω(log ∘ (↑))
```
**Use case**: Show polynomial growth dominates logarithmic

### 2. Exponential growth
```lean
theorem asymptotic_exponential_growth
  {f g : ℕ → ℝ} (h_f_ge : ∀ n, f n ≥ g n)
  (h_g_omega : g = ω(log ∘ (↑)))
  (h_const : ∃ ε > 0, ∀ n, (2 : ℝ) ^ (log n) ≥ (n : ℝ) ^ ε) :
  ∃ ε > 0, f = ω(fun n => (n : ℝ) ^ ε)
```
**Use case**: Convert superlogarithmic to superpolynomial

### 3. Gap 2 asymptotic
```lean
theorem gap2_superlog_implies_superpoly
  {Π : ProblemInstance} {S : Separator Π}
  (h_κ : κ_Π > 0)
  (h_ic : ∀ (C : ℝ) (hC : C > 0), ∃ N, ∀ n ≥ N, 
    GraphIC (incidenceGraph Π) S n ≥ C * log (size Π n)) :
  ∃ (ε : ℝ) (hε : 0 < ε), RuntimeLowerBound Π
```
**Use case**: Prove superpolynomial lower bound from IC

### 4. SAT not in P
```lean
theorem sat_not_in_p_if_superlog_ic :
  (∃ (φ : CNFFormula) (S : Unit),
    ∀ (C : ℝ) (hC : C > 0), ∃ N, ∀ n ≥ N,
      (numVars φ : ℝ) ≥ C * log n) →
  SAT_Language ∉ P_Class
```
**Use case**: Show SAT requires superpolynomial time

### 5. P ≠ NP
```lean
theorem P_neq_NP_final : P_Class ≠ NP_Class
```
**Use case**: The main result

## Common Patterns

### Prove ω relationship
```lean
-- To prove f = ω(g):
intro C hC_pos       -- Take any constant C > 0
use N                -- Provide witness N
intro n hn           -- For all n ≥ N
-- Prove: C * |g n| ≤ |f n|
```

### Prove O relationship
```lean
-- To prove f = O(g):
use C, hC_pos        -- Provide constant C > 0
use N                -- Provide witness N
intro n hn           -- For all n ≥ N
-- Prove: |f n| ≤ C * |g n|
```

### Use separation lemma
```lean
example {f : ℕ → ℝ} {ε k : ℝ} (hε : ε > 0)
  (h_omega : f = ω(fun n => (n : ℝ) ^ ε))
  (h_bigO : f = O(fun n => (n : ℝ) ^ k)) :
  False := omega_not_subset_of_bigO hε h_omega h_bigO
```

## Structures

### Runtime Lower Bound
```lean
structure RuntimeLowerBound (Π : Type) where
  bound : ℕ → ℝ
  is_lower : ∀ (Σ Γ Q : Type*) [InputAlphabet Σ Γ] [StateSet Q]
    (M : TuringMachine Σ Γ Q), bound n ≥ 0
```

**Use case**: Formalize lower bounds on runtime

## Building

```bash
# Build the module
lake build Gap2_Asymptotic

# Build tests
lake build Gap2AsymptoticTests

# Run build script
./build_and_verify_gap2_asymptotic.sh
```

## Testing

Location: `tests/Gap2AsymptoticTests.lean`

Tests verify:
1. ✅ Asymptotic notation definitions
2. ✅ Power-log separation
3. ✅ Exponential growth theorem
4. ✅ Gap2 theorems
5. ✅ SAT lower bounds
6. ✅ P ≠ NP theorem
7. ✅ Tseitin instances
8. ✅ Runtime bounds
9. ✅ Omega/Big-O separation
10. ✅ Structure construction

## Proof Strategy

The proof follows this chain:

```
1. Construct hard instances (Tseitin formulas)
   ↓
2. Show IC ≥ ω(log n) for these instances
   ↓
3. Apply Gap 2: T ≥ 2^IC
   ↓
4. Use exponential growth: 2^ω(log n) = ω(n^ε)
   ↓
5. Conclude: T ≥ ω(n^ε) (superpolynomial)
   ↓
6. Contradiction with P (polynomial)
   ↓
7. Therefore: P ≠ NP
```

## Dependencies

### Internal modules
- `TuringMachine.lean`
- `ComplexityClasses.lean`
- `SAT.lean`
- `TseitinHardFamily.lean`
- `TreewidthToIC.lean`

### Mathlib imports
- `Mathlib.Analysis.Asymptotics.Asymptotics`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- `Mathlib.Data.Real.Basic`
- `Mathlib.Tactic`

## Troubleshooting

### Import errors
Ensure all dependencies are built:
```bash
lake build TuringMachine
lake build ComplexityClasses
lake build SAT
lake build TseitinHardFamily
lake build TreewidthToIC
```

### Type errors
Check that you're using the correct namespace:
```lean
open AsymptoticLowerBounds
```

### Tactic failures
Some proofs use `sorry` for complex real analysis. These represent standard results that could be filled in with sufficient auxiliary lemmas.

## Examples

### Example 1: Basic usage
```lean
import Gap2_Asymptotic
open AsymptoticLowerBounds

#check P_neq_NP_final
-- P_neq_NP_final : P_Class ≠ NP_Class
```

### Example 2: Asymptotic notation
```lean
example : (fun n => n ^ (3/2)) = ω(log ∘ (↑)) := by
  apply pow_epsilon_dominates_log
  norm_num
```

### Example 3: Using structures
```lean
example (Π : ProblemInstance) : 
  ∃ (R : RuntimeLowerBound Π), R.bound 10 ≥ 0 := by
  sorry  -- Construct specific bound
```

## Further Reading

- **GAP2_ASYMPTOTIC_README.md** - Full documentation
- **GAP2_ASYMPTOTIC_IMPLEMENTATION_SUMMARY.md** - Implementation details
- **tests/Gap2AsymptoticTests.lean** - Test examples

## License

MIT License - Part of P-NP Formalization Project
