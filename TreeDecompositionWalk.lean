/-!
# Tree Decomposition with Native Walk API (Running Intersection)

This module formalizes a tree decomposition structure that includes the
**running intersection** property, expressed directly via Mathlib's native
`SimpleGraph.Walk` API (`p.IsPath` and `p.support`).

## Key design

* Tree nodes are indexed by `ℕ`.
* Bags are `ℕ → Finset V`.
* `running_intersection` uses the native `SimpleGraph.Walk` API:
  for any simple path `p` from bag-node `t1` to `t2`, every vertex
  present in both `X t1` and `X t2` must also appear in every bag `X t3`
  with `t3 ∈ p.support`.

## Main results

* `TreeDecompRI` — structure with full running intersection property.
* `treewidthRI` — treewidth via `sInf`.
* `treewidthRI_pos_of_has_edge` — any graph with an edge has treewidth ≥ 1.

## Status: 0 sorries (uses `PathGraphAcyclic.natPathGraph_isTree`)

∞³ 141.7001 Hz - JMMB Ψ
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Tactic
import PathGraphAcyclic

namespace TreeDecompositionWalk

open NatPath SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The core structure -/

/--
Tree decomposition of `G` with the native `SimpleGraph.Walk` running intersection.

Fields:
* `T`     — auxiliary tree (a `SimpleGraph ℕ`)
* `T_tree` — proof that `T` is indeed a tree
* `X`     — bag assignment: each tree-node `t : ℕ` gets a bag `X t ⊆ V`
* `vertex_covered` — every vertex of `G` appears in some bag
* `edge_covered`   — every edge of `G` is covered by some bag
* `running_intersection` — the coherence property expressed via walks:
  if `p` is a *simple* path from `t1` to `t2` and `t3 ∈ p.support`,
  then `X t1 ∩ X t2 ⊆ X t3`.
-/
structure TreeDecompRI (G : SimpleGraph V) where
  /-- Auxiliary tree on ℕ-indexed nodes -/
  T        : SimpleGraph ℕ
  /-- The auxiliary graph must be a tree -/
  T_tree   : T.IsTree
  /-- Bag assignment -/
  X        : ℕ → Finset V
  /-- Vertex coverage: every v ∈ V appears in some bag -/
  vertex_covered : ∀ v : V, ∃ t : ℕ, v ∈ X t
  /-- Edge coverage: every edge {v,w} of G is covered by some bag -/
  edge_covered   : ∀ ⦃v w : V⦄, G.Adj v w → ∃ t : ℕ, v ∈ X t ∧ w ∈ X t
  /--
  **Running intersection** (coherence property) via the native Walk API:
  for any *path* `p` from tree-node `t1` to `t2`, and any `t3` on this path,
  the intersection `X t1 ∩ X t2` is contained in `X t3`.

  This is the standard separation / coherence axiom of tree decompositions.
  -/
  running_intersection : ∀ (t1 t2 t3 : ℕ) (p : T.Walk t1 t2),
      p.IsPath → t3 ∈ p.support → X t1 ∩ X t2 ⊆ X t3

/-! ## Width and treewidth -/

/--
Width of a `TreeDecompRI`: `(⨆ t, |X t|) − 1`.

We use `⨆` (iSup) instead of `Finset.sup Finset.univ` because the tree-node
index type `ℕ` is infinite (not a `Fintype`).
-/
noncomputable def decompWidthRI {G : SimpleGraph V} (D : TreeDecompRI G) : ℕ :=
  (⨆ t : ℕ, (D.X t).card) - 1

/--
Treewidth of `G` via `sInf`: the minimum width over all `TreeDecompRI` decompositions.
-/
noncomputable def treewidthRI (G : SimpleGraph V) : ℕ :=
  sInf { k | ∃ D : TreeDecompRI G, decompWidthRI D = k }

/-! ## Trivial decomposition -/

/--
**Trivial decomposition**: every bag is `Finset.univ` (all vertices), and the
auxiliary tree is the infinite path graph on `ℕ`.

The running intersection holds because
`X t1 ∩ X t2 = Finset.univ ∩ Finset.univ = Finset.univ = X t3`.
-/
noncomputable def trivialDecompRI (G : SimpleGraph V) : TreeDecompRI G where
  T              := natPathGraph
  T_tree         := natPathGraph_isTree
  X              := fun _ => Finset.univ
  vertex_covered := fun v => ⟨0, Finset.mem_univ v⟩
  edge_covered   := fun v w _ => ⟨0, Finset.mem_univ v, Finset.mem_univ w⟩
  running_intersection := fun _ _ _ _ _ _ => by
    -- X t = Finset.univ for all t; univ ∩ univ ⊆ univ is trivial
    simp [Finset.inter_self]

/-! ## The width set is nonempty -/

lemma decompWidthRI_set_nonempty (G : SimpleGraph V) :
    { k | ∃ D : TreeDecompRI G, decompWidthRI D = k }.Nonempty :=
  ⟨_, trivialDecompRI G, rfl⟩

/-! ## Auxiliary lemma: two distinct elements give card ≥ 2 -/

private lemma finset_card_ge_two {α : Type*} {s : Finset α} {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : 2 ≤ s.card := by
  have hcard2 : ({a, b} : Finset α).card = 2 := Finset.card_pair hab
  linarith [Finset.card_le_card
    (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)]

/-! ## Main theorem -/

/--
**Theorem**: If `G` has at least one edge, then `treewidthRI G ≥ 1`.

**Proof sketch**:
1. Any edge `{v, w}` must be covered by some bag `X t` in every decomposition.
2. Since `v ≠ w` (simple graph), the bag has at least 2 elements, so
   `(⨆ s, |X s|) ≥ 2`, giving `decompWidthRI ≥ 1`.
3. The `sInf` of a nonempty set of naturals all `≥ 1` is itself `≥ 1`
   (by `Nat.le_csInf`).
-/
theorem treewidthRI_pos_of_has_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∃ v w : V, G.Adj v w) : treewidthRI G ≥ 1 := by
  obtain ⟨v, w, h_adj⟩ := h
  apply Nat.le_csInf (decompWidthRI_set_nonempty G)
  -- Show every element of the width-set is ≥ 1
  intro k ⟨D, hD⟩
  rw [← hD]
  -- The edge {v, w} is covered by some bag at tree-node t
  obtain ⟨t, hv, hw⟩ := D.edge_covered h_adj
  -- v ≠ w because G is a simple graph
  have hne : v ≠ w := G.ne_of_adj h_adj
  -- The bag X t has at least 2 elements
  have hcard : 2 ≤ (D.X t).card := finset_card_ge_two hv hw hne
  -- The iSup is at least as large as any single bag
  have hiSup : 2 ≤ ⨆ s : ℕ, (D.X s).card := le_iSup_of_le t hcard
  -- Therefore decompWidthRI = iSup - 1 ≥ 1
  simp only [decompWidthRI]
  omega

end TreeDecompositionWalk
