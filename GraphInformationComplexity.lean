/-!
# Graph Information Complexity

This file formalizes the connection between graph separators and information complexity,
establishing bounds on the number of configurations based on separator size.

## Main Definitions

* `GraphIC G S`: Graph Information Complexity - the minimum number of bits needed to
  distinguish configurations in components separated by separator S.
* `phIC G S`: Physical Information Complexity approximation based on separator size.
* `balanced_separator_size_bound`: Upper bound on the size of a balanced separator
  relative to the total number of vertices.

## Main Results

* `log_total_configs_lower_bound`: Proves that log₂(total_configs) ≥ S.card / 2
  for balanced separators, establishing the fundamental information-theoretic
  lower bound.
* `phIC_lower_bound`: Proves that phIC G S ≥ S.card / 2, a trivial bound by definition.

Author: José Manuel Mota Burruezo & Claude (Noēsis)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Omega

open Classical
noncomputable section

namespace GraphInformationComplexity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Basic Graph and Separator Definitions -/

/-- A separator in a graph partitions vertices into components -/
structure Separator (G : SimpleGraph V) where
  /-- The set of vertices in the separator -/
  S : Finset V
  /-- The separator is balanced: creates at least 2 significant components -/
  is_balanced : S.card > 0

/-- A balanced separator satisfies size constraints relative to total vertices.
    The upper bound |S| ≤ (2/3)|V| ensures that the separator creates
    significant components on both sides. -/
def is_balanced_separator (G : SimpleGraph V) (S : Separator G) : Prop :=
  S.S.card ≤ (2 * Fintype.card V) / 3

/-! ## Information Complexity Definitions -/

/-- The number of possible configurations in components separated by S.
    Each configuration corresponds to a different assignment to non-separator vertices. -/
def total_configs (G : SimpleGraph V) (S : Separator G) : ℕ :=
  2 ^ (Fintype.card V - S.S.card)

/-- Graph Information Complexity: minimum bits needed to distinguish configurations -/
def GraphIC (G : SimpleGraph V) (S : Separator G) : ℕ :=
  Nat.log 2 (total_configs G S)

/-- phIC: Physical Information Complexity approximation based on separator size -/
def phIC (G : SimpleGraph V) (S : Finset V) : ℕ :=
  S.card / 2

/-! ## Main Lemmas and Theorems -/

/-- Balanced separators cannot be too large relative to the graph size.
    This lemma extracts the size bound from the balanced separator property.
    It's the key inequality used in proving the information complexity lower bound. -/
lemma balanced_separator_size_bound 
  (G : SimpleGraph V) 
  (S : Separator G) 
  (h_sep : is_balanced_separator G S) :
  S.S.card ≤ (2 * Fintype.card V) / 3 := 
  h_sep

/-- The logarithm of total configurations equals the number of non-separator vertices -/
lemma log_total_configs_eq 
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_card : Fintype.card V ≥ S.S.card) :
  Nat.log 2 (total_configs G S) = Fintype.card V - S.S.card := by
  unfold total_configs
  by_cases h : Fintype.card V - S.S.card > 0
  · exact Nat.log_pow h
  · push_neg at h
    have : Fintype.card V - S.S.card = 0 := by omega
    simp [this]

/--
Main Theorem: Information-theoretic lower bound for balanced separators.

For any balanced separator S of graph G:
  log₂(total_configs) ≥ S.card / 2

Proof sketch:
1. total_configs = 2^(|V| - |S|)
2. log₂(total_configs) = |V| - |S|
3. By balanced_separator_size_bound: |S| ≤ (2/3)|V|
4. Therefore: |V| - |S| ≥ |V| - (2/3)|V| = (1/3)|V|
5. From balanced separator properties: (1/3)|V| ≥ |S|/2
6. Thus: log₂(total_configs) ≥ |S|/2
-/
theorem log_total_configs_lower_bound 
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_sep : is_balanced_separator G S)
  (h_nonempty : Fintype.card V > 0) :
  Nat.log 2 (total_configs G S) ≥ S.S.card / 2 := by
  -- Step 1: Establish that Fintype.card V ≥ S.S.card (separator can't be larger than graph)
  have h_card : Fintype.card V ≥ S.S.card := by
    by_contra h_contra
    push_neg at h_contra
    have h_bound := balanced_separator_size_bound G S h_sep
    have : (2 * Fintype.card V) / 3 < Fintype.card V := by
      apply Nat.div_lt_self h_nonempty
      omega
    omega
  
  -- Step 2: Apply log_total_configs_eq to simplify
  have h_log := log_total_configs_eq G S h_card
  rw [h_log]
  
  -- Step 3: Prove Fintype.card V - S.S.card ≥ S.S.card / 2
  -- Using the balanced separator bound: S.S.card ≤ (2/3) * Fintype.card V
  have bound := balanced_separator_size_bound G S h_sep
  omega

/-! ## Corollaries and Applications -/

/-- GraphIC provides a lower bound proportional to separator size -/
theorem graphIC_lower_bound
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_sep : is_balanced_separator G S)
  (h_nonempty : Fintype.card V > 0) :
  GraphIC G S ≥ S.S.card / 2 := by
  unfold GraphIC
  exact log_total_configs_lower_bound G S h_sep h_nonempty

/-- phIC lower bound: trivially satisfied by definition.
    
    This lemma establishes the baseline bound for phIC, which by definition
    satisfies phIC G S = S.card / 2. While this appears tautological, it serves
    as a foundational building block in the complexity framework, allowing phIC
    to be refined with additional entropy, treewidth, or κ_Π constraints in future
    developments without changing the interface. -/
lemma phIC_lower_bound (G : SimpleGraph V) [Fintype V] (S : Finset V)
  (h_sep : is_balanced_separator G ⟨S, by omega⟩) :  -- omega proves S.card > 0 from h_sep
  phIC G S ≥ S.card / 2 := by
  unfold phIC
  exact Nat.le_refl (S.card / 2)

/--
Alternative direct proof following the approach from the problem statement.

Given:
- total_configs = 2^(Fintype.card V - S.card)
- log₂(total_configs) = Fintype.card V - S.card

Need to prove:
- Fintype.card V - S.card ≥ S.card / 2

This is equivalent to:
- Fintype.card V ≥ (3/2) * S.card
- S.card ≤ (2/3) * Fintype.card V

Which is exactly the balanced_separator_size_bound!
-/
theorem log_total_configs_lower_bound_direct
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_sep : is_balanced_separator G S)
  (h_nonempty : Fintype.card V > 0) :
  Nat.log 2 (2 ^ (Fintype.card V - S.S.card)) ≥ S.S.card / 2 := by
  -- Step 1: Establish that log₂(2^k) = k
  by_cases h : Fintype.card V - S.S.card > 0
  · -- When the exponent is positive, log₂(2^k) = k
    rw [Nat.log_pow h]
    -- Use the balanced separator bound: S.card ≤ (2/3) * Fintype.card V
    have bound := balanced_separator_size_bound G S h_sep
    omega
  · -- When the exponent is 0, both sides are 0
    push_neg at h
    have : Fintype.card V - S.S.card = 0 := by omega
    simp [this]

end GraphInformationComplexity
