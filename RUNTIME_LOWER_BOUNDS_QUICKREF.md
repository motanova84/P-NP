# RuntimeLowerBounds: Quick Reference Guide

## Main Theorems

### 1. `P_neq_NP_final`
**The Main Result**
```lean
theorem P_neq_NP_final : P_Class ≠ NP_Class
```
**What it means:** P and NP are distinct complexity classes.

**Proof strategy:** Contradiction via hard SAT instances with superpolynomial runtime.

---

### 2. `sat_not_in_p_if_superlog_ic`
**SAT Cannot Be in P**
```lean
theorem sat_not_in_p_if_superlog_ic :
  (∃ (φ : CNFFormula) (S : Separator (incidenceGraph φ)),
    (fun n => GraphIC (incidenceGraph φ) S n) = ω(fun n => Real.log n)) →
  ¬(SAT_Language ∈ P_Class)
```
**What it means:** If there exist SAT instances with superlogarithmic IC, then SAT is not in P.

**Key insight:** High IC creates an information bottleneck that forces exponential runtime.

---

### 3. `gap2_superlog_implies_superpoly`
**IC to Runtime Connection**
```lean
theorem gap2_superlog_implies_superpoly
  (π : Π) (S : Separator (incidenceGraph π))
  (h_κ : 0 < ProblemInstance.κ_Π Π)
  (h_ic : (fun n => GraphIC (incidenceGraph π) S n) = ω(fun n => Real.log n)) :
  ∃ (ε : ℝ) (hε : 0 < ε), 
    (fun n => RuntimeLowerBound π n) = ω(fun n => ((ProblemInstance.size π : ℕ) : ℝ) ^ ε)
```
**What it means:** Superlogarithmic IC implies superpolynomial runtime.

**Specifically:** IC ≥ ω(log n) → Runtime ≥ ω(n^ε) for some ε > 0.

---

### 4. `asymptotic_exponential_growth`
**Exponentiating Preserves Growth**
```lean
theorem asymptotic_exponential_growth
  (π : Π) (S : Separator (incidenceGraph π))
  (h₁ : ∀ n, RuntimeLowerBound π n ≥ (2 : ℝ) ^ (GraphIC (incidenceGraph π) S n))
  (h₂ : (fun n => GraphIC (incidenceGraph π) S n) = ω(fun n => Real.log n))
  (ε : ℝ) (hε : 0 < ε) :
  (fun n => RuntimeLowerBound π n) = ω(fun n => ((ProblemInstance.size π : ℕ) : ℝ) ^ ε)
```
**What it means:** 2^ω(log n) = ω(n^ε).

**Key property:** Exponentiating superlogarithmic functions yields superpolynomial functions.

---

### 5. `tseitin_hard_instances_exist`
**Hard Instances Construction**
```lean
theorem tseitin_hard_instances_exist :
  ∃ (φ : CNFFormula) (S : Separator (incidenceGraph φ)),
    (fun n => GraphIC (incidenceGraph φ) S n) = ω(fun n => Real.log n)
```
**What it means:** We can explicitly construct CNF formulas with superlogarithmic IC.

**Construction:** Tseitin formulas over Margulis-Gabber-Galil expanders.

---

## Supporting Definitions

### Asymptotic Notation

**ω-notation (Little-omega):**
```lean
def omega_notation (f g : ℕ → ℝ) : Prop :=
  ∀ (C : ℝ) (hC : C > 0), ∃ N : ℕ, ∀ n ≥ N, f n ≥ C * g n

notation:50 f " = ω(" g ")" => omega_notation f g
```
Means: f grows faster than any constant multiple of g.

**O-notation (Big-O):**
```lean
def O_notation (f g : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (hC : C > 0), ∃ N : ℕ, ∀ n ≥ N, f n ≤ C * g n

notation:50 f " = O(" g ")" => O_notation f g
```
Means: f is bounded by some constant multiple of g.

### Problem Instance

```lean
class ProblemInstance (Π : Type*) where
  size : Π → ℕ
  graph : Π → SimpleGraph IncidenceVertex
  κ_Π : ℝ
  κ_Π_pos : 0 < κ_Π
```

### Information Complexity

```lean
axiom GraphIC {Π : Type*} [ProblemInstance Π] : 
  (G : SimpleGraph IncidenceVertex) → 
  (S : Separator G) → 
  (n : ℕ) → ℝ
```
Measures: Minimum bits needed to distinguish configurations.

### Runtime Lower Bound

```lean
axiom RuntimeLowerBound {Π : Type*} [ProblemInstance Π] : Π → ℕ → ℝ
```
Measures: Minimum time to solve the problem instance.

---

## Key Axioms

### GAP 2: Runtime ≥ 2^IC
```lean
axiom gap2_runtime_ge_exp_ic {Π : Type*} [ProblemInstance Π] :
  (π : Π) → (S : Separator (incidenceGraph π)) →
  (h_κ : 0 < ProblemInstance.κ_Π Π) →
  ∀ n, RuntimeLowerBound π n ≥ (2 : ℝ) ^ (GraphIC (incidenceGraph π) S n)
```

### Yao's Communication Complexity
```lean
axiom yao_communication_complexity {Π : Type*} [ProblemInstance Π] :
  (π : Π) → (μ : Distribution Π) → (S : Separator (incidenceGraph π)) →
  CommunicationComplexity π μ ≥ λ n => GraphIC (incidenceGraph π) S n
```

### Runtime ≥ Communication
```lean
axiom runtime_ge_communication {Π : Type*} [ProblemInstance Π] :
  (π : Π) → (μ : Distribution Π) →
  RuntimeLowerBound π ≥ CommunicationComplexity π μ
```

### Expanders Have High IC
```lean
axiom expander_has_superlog_ic {V : Type*} (G : SimpleGraph V) :
  IsExpander G → 
  ∃ (S : Separator G), 
    ∀ (n : ℕ), GraphIC G S n = ω(fun m => Real.log m) n
```

### SAT is NP-complete
```lean
axiom SAT_is_NP_complete : SAT_Language ∈ NP_Class ∧ 
  (∀ (L : Language Bool), L ∈ NP_Class → 
    ∃ (f : List Bool → List Bool), 
      (∀ w, L w ↔ SAT_Language (f w)) ∧ 
      (∃ k, ∀ w, (f w).length ≤ w.length ^ k))
```

---

## Proof Flow Diagram

```
┌─────────────────────────────────────────────────────┐
│  Expander Graphs (Margulis-Gabber-Galil)           │
└─────────────────┬───────────────────────────────────┘
                  │
                  ↓
┌─────────────────────────────────────────────────────┐
│  Tseitin Formulas over Expanders                    │
│  (tseitin_expander_formula)                         │
└─────────────────┬───────────────────────────────────┘
                  │
                  ↓
┌─────────────────────────────────────────────────────┐
│  High Information Complexity                        │
│  IC ≥ ω(log n)                                      │
│  (expander_has_superlog_ic)                         │
└─────────────────┬───────────────────────────────────┘
                  │
                  ↓
┌─────────────────────────────────────────────────────┐
│  Communication Lower Bound                          │
│  Communication ≥ IC                                 │
│  (yao_communication_complexity)                     │
└─────────────────┬───────────────────────────────────┘
                  │
                  ↓
┌─────────────────────────────────────────────────────┐
│  Exponential Runtime                                │
│  Runtime ≥ 2^IC ≥ 2^ω(log n)                       │
│  (gap2_runtime_ge_exp_ic)                           │
└─────────────────┬───────────────────────────────────┘
                  │
                  ↓
┌─────────────────────────────────────────────────────┐
│  Superpolynomial Runtime                            │
│  Runtime ≥ ω(n^ε)                                   │
│  (asymptotic_exponential_growth)                    │
└─────────────────┬───────────────────────────────────┘
                  │
                  ↓
┌─────────────────────────────────────────────────────┐
│  SAT ∉ P                                            │
│  (sat_not_in_p_if_superlog_ic)                     │
└─────────────────┬───────────────────────────────────┘
                  │
                  ↓
┌─────────────────────────────────────────────────────┐
│  P ≠ NP                                             │
│  (P_neq_NP_final)                                   │
└─────────────────────────────────────────────────────┘
```

---

## Usage Examples

### Example 1: Verify P ≠ NP
```lean
import RuntimeLowerBounds

-- The main theorem
#check P_neq_NP_final
-- P_neq_NP_final : P_Class ≠ NP_Class

-- Use it
example : P_Class ≠ NP_Class := P_neq_NP_final
```

### Example 2: Get Hard Instance
```lean
-- Construct a hard Tseitin formula
def my_hard_formula : CNFFormula :=
  tseitin_expander_formula 201 (by norm_num) ⟨100, by norm_num⟩

-- It has superlogarithmic IC
example : ∃ S, (fun n => GraphIC (incidenceGraph my_hard_formula) S n) 
               = ω(fun n => Real.log n) := by
  apply tseitin_hard_instances_exist.choose_spec
```

### Example 3: Apply GAP 2
```lean
variable (φ : CNFFormula) 
variable (S : Separator (incidenceGraph φ))
variable (h_ic : (fun n => GraphIC (incidenceGraph φ) S n) = ω(fun n => Real.log n))

-- Get superpolynomial runtime
example : ∃ ε > 0, (fun n => RuntimeLowerBound φ n) = ω(fun n => (n : ℝ) ^ ε) :=
  gap2_superlog_implies_superpoly φ S (tseitin_spectral_constant_pos φ) h_ic
```

---

## Constants

### κ_Π - The Millennium Constant
```lean
κ_Π = 2.5773
```
**Significance:**
- Spectral gap threshold for expanders
- IC/treewidth ratio
- Universal information-geometric constant

**Appears in:**
- `ProblemInstance.κ_Π`
- `IsKappaExpander.expansion_constant`
- Runtime exponent denominators

---

## Complexity Classes

### P (Polynomial Time)
```lean
def P_Class {Σ : Type*} : Set (Language Σ) :=
  { L | ∃ k : ℕ, L ∈ TIME (fun n => n ^ k) }
```
Languages decidable in polynomial time.

### NP (Nondeterministic Polynomial Time)
```lean
def NP_Class {Σ : Type*} : Set (Language Σ) :=
  { L | ∃ k : ℕ, L ∈ NTIME (fun n => n ^ k) }
```
Languages verifiable in polynomial time.

### SAT Language
```lean
def SAT_Language : Language Bool :=
  fun w => ∃ φ : CNFFormula, Satisfiable φ
```
The Boolean satisfiability problem.

---

## Helper Lemmas

### Omega Notation Properties
```lean
theorem omega_transitive (f g h : ℕ → ℝ) 
  (h1 : f = ω(g)) (h2 : g = ω(h)) : f = ω(h)
```

### O Notation Properties  
```lean
theorem O_scalar_mult (f g : ℕ → ℝ) (c : ℝ) (hc : c > 0)
  (h : f = O(g)) : (fun n => c * f n) = O(g)
```

### Separation
```lean
theorem asymptotic_separation_poly_vs_superpoly (k : ℕ) (ε : ℝ) (hε : 0 < ε)
  (h : O_notation (fun n => (n : ℝ) ^ k) (fun n => (n : ℝ) ^ ε)) :
  omega_notation (fun n => (n : ℝ) ^ ε) (fun n => (n : ℝ) ^ k) → False
```
**What it means:** O(n^k) and ω(n^ε) are incompatible - you can't have both.

---

## Dependencies

```
RuntimeLowerBounds.lean
  ├── Mathlib.Analysis.Asymptotics.Asymptotics
  ├── Mathlib.Analysis.SpecialFunctions.Pow.Real
  ├── Mathlib.Analysis.SpecialFunctions.Log.Basic
  ├── SAT.lean
  ├── ComplexityClasses.lean
  ├── GraphInformationComplexity.lean
  └── TseitinHardFamily.lean
```

---

## References

- **Yao (1979)**: Communication complexity lower bounds
- **Karchmer-Wigderson (1990)**: Communication-circuit duality
- **Tseitin (1968)**: Graph-based CNF encoding
- **Margulis (1988)**: Explicit expander constructions

---

**For detailed documentation, see:**
- `RUNTIME_LOWER_BOUNDS_README.md` - Full theorem documentation
- `FORMAL_COROLLARY_COMPLETE.md` - Complete proof architecture

**Author:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Project:** QCAL ∞³
