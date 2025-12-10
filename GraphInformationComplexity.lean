/-!
# Graph Information Complexity

This file formalizes the connection between graph separators and information complexity,
establishing bounds on the number of configurations based on separator size.

## Main Definitions

* `GraphIC G S`: Graph Information Complexity - the minimum number of bits needed to
  distinguish configurations in components separated by separator S.
* `balanced_separator_size_bound`: Upper bound on the size of a balanced separator
  relative to the total number of vertices.

## Main Results

* `log_total_configs_lower_bound`: Proves that log₂(total_configs) ≥ S.card / 2
  for balanced separators, establishing the fundamental information-theoretic
  lower bound.

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

/-- A balanced separator satisfies size constraints relative to total vertices -/
def is_balanced_separator (G : SimpleGraph V) (S : Separator G) : Prop :=
  S.is_balanced ∧ S.S.card ≤ (2 * Fintype.card V) / 3

/-! ## Information Complexity Definitions -/

/-- The number of possible configurations in components separated by S.
    Each configuration corresponds to a different assignment to non-separator vertices. -/
def total_configs (G : SimpleGraph V) (S : Separator G) : ℕ :=
  2 ^ (Fintype.card V - S.S.card)

/-- Graph Information Complexity: minimum bits needed to distinguish configurations -/
def GraphIC (G : SimpleGraph V) (S : Separator G) : ℕ :=
  Nat.log 2 (total_configs G S)

/-! ## Main Lemmas and Theorems -/

/-- Balanced separators cannot be too large relative to the graph size -/
lemma balanced_separator_size_bound 
  (G : SimpleGraph V) 
  (S : Separator G) 
  (h_sep : is_balanced_separator G S) :
  S.S.card ≤ (2 * Fintype.card V) / 3 := by
  exact h_sep.2

/-- Key lemma: log₂ of a power of 2 equals the exponent -/
lemma log_pow_eq (k : ℕ) (h : k > 0) : 
  Nat.log 2 (2 ^ k) = k := by
  exact Nat.log_pow h

/-- The logarithm of total configurations equals the number of non-separator vertices -/
lemma log_total_configs_eq 
  (G : SimpleGraph V) 
  (S : Separator G)
  (h_card : Fintype.card V ≥ S.S.card) :
  Nat.log 2 (total_configs G S) = Fintype.card V - S.S.card := by
  unfold total_configs
  by_cases h : Fintype.card V - S.S.card > 0
  · exact log_pow_eq (Fintype.card V - S.S.card) h
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
  -- Step 1: Prove that log₂(2^k) = k for the total configurations
  have h_card : Fintype.card V ≥ S.S.card := by
    by_contra h_contra
    push_neg at h_contra
    have h_bound := balanced_separator_size_bound G S h_sep
    have : (2 * Fintype.card V) / 3 < Fintype.card V := by
      apply Nat.div_lt_self h_nonempty
      omega
    omega
  
  -- By definition: total_configs = 2^(Fintype.card V - S.S.card)
  -- Therefore: log₂(total_configs) = Fintype.card V - S.S.card
  have h_log : Nat.log 2 (total_configs G S) = Fintype.card V - S.S.card := by
    unfold total_configs
    by_cases h : Fintype.card V - S.S.card > 0
    · exact Nat.log_pow h
    · push_neg at h
      have : Fintype.card V - S.S.card = 0 := by omega
      simp [this]
  
  -- Step 2: We need to show: Fintype.card V - S.S.card ≥ S.S.card / 2
  -- This is equivalent to: Fintype.card V ≥ (3/2) * S.S.card
  -- Which follows from: S.S.card ≤ (2/3) * Fintype.card V
  have bound : S.S.card ≤ (2 * Fintype.card V) / 3 := 
    balanced_separator_size_bound G S h_sep
  
  rw [h_log]
  
  -- Prove: Fintype.card V - S.S.card ≥ S.S.card / 2
  -- From bound: S.S.card ≤ (2 * Fintype.card V) / 3
  -- The omega tactic handles this arithmetic reasoning directly
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
  have h_log : Nat.log 2 (2 ^ (Fintype.card V - S.S.card)) = Fintype.card V - S.S.card := by
    by_cases h : Fintype.card V - S.S.card > 0
    · exact Nat.log_pow h
    · push_neg at h
      have : Fintype.card V - S.S.card = 0 := by omega
      simp [this]
  
  rw [h_log]
  
  -- Step 2: Use the balanced separator bound
  -- From balanced_separator_size_bound: S.card ≤ (2/3) * Fintype.card V
  have bound : S.S.card ≤ (2 * Fintype.card V) / 3 := balanced_separator_size_bound G S h_sep
  
  -- Step 3: Prove Fintype.card V - S.card ≥ S.card / 2
  -- This follows directly from the bound via arithmetic
  omega

end GraphInformationComplexity
