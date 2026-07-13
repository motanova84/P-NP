/-!
# Path Graph Acyclicity

Pure combinatorial proof that the finite path graph on `n` vertices is acyclic.

This fills the `sorry` in `CycleTreeDecomposition.lean` (`tree_is_acyclic`)
and `SimpleTreewidth.lean` (`pathGraph_is_tree`).

## Strategy

**Step 1 — Discrete IVT.**  Any walk in the path graph from vertex `a` to vertex `b`
(with `b.val < k < a.val`) contains a vertex with value `k`.
Proved by structural induction on the walk.

**Step 2 — Main theorem.**  Suppose for contradiction that `c : Walk v v` is a cycle.
Write `c = cons hadj q`.  From `cons_isCycle_iff`:
- `q.IsPath`   (each vertex visited at most once, in particular `q.support.Nodup`)
- `s(v, w) ∉ q.edges`   (the opening edge `{v, w}` is not reused)

Reverse `q` to inspect its last step:  `q.reverse = cons hadj_last r`.
The last edge `s(v, z)` of `q` must differ from `s(v, w)` (trail condition),
so `z ≠ w` and therefore `z` lies on the *opposite* side of `v` from `w`.
By the IVT, `v` appears in `r.support`.  But `q.support.Nodup` and
`q.support.reverse = v :: r.support` imply `v ∉ r.support`.  Contradiction.

## Author
JMMB & GitHub Copilot
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace PNP

open SimpleGraph Walk

/-! ## Local path graph definition

This matches both `SimpleTreewidth.pathGraph` and `CycleTreeDecomposition.treeStructure`.
-/

/-- Path graph on `n` vertices: vertex `i` is adjacent to `i ± 1`. -/
def localPathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm    := fun _ _ h ↦ h.symm
  loopless := fun _ h ↦ by rcases h with h | h <;> omega

/-! ## Discrete Intermediate Value Theorem -/

/--
**Discrete IVT (downward direction).**

In `localPathGraph n`, any walk from `a` to `b` with `b.val < k < a.val`
contains a vertex with value `k`.
-/
private lemma localPathGraph_walk_ivt
    {n : ℕ} {a b : Fin n}
    (q : (localPathGraph n).Walk a b)
    {k : ℕ} (hlo : b.val < k) (hhi : k < a.val) :
    ∃ u ∈ q.support, u.val = k := by
  induction q with
  | nil =>
    -- nil walk: a = b, so b.val < k < b.val — impossible
    exact absurd hhi (by omega)
  | @cons _ a c _ hadj r ih =>
    -- Unfold the adjacency predicate of localPathGraph
    have hadj_vals : a.val + 1 = c.val ∨ c.val + 1 = a.val := hadj
    simp only [Walk.support_cons, List.mem_cons]
    rcases hadj_vals with h | h
    · -- Right step: c.val = a.val + 1  (moving away from b)
      -- k < a.val < c.val, apply IH to r : Walk c b
      obtain ⟨u, hu, huv⟩ := ih hlo (by omega : k < c.val)
      exact ⟨u, .inr hu, huv⟩
    · -- Left step: c.val + 1 = a.val  (c.val = a.val - 1, moving toward b)
      -- k ≤ c.val since k < a.val = c.val + 1
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hhi) with rfl | hlt
      · -- k = c.val: c is the start of r
        exact ⟨c, .inr (Walk.start_mem_support r), rfl⟩
      · -- k < c.val: apply IH to r : Walk c b
        obtain ⟨u, hu, huv⟩ := ih hlo hlt
        exact ⟨u, .inr hu, huv⟩

/-! ## Path graph is acyclic -/

/-- **Main theorem**: the path graph on `n` vertices is acyclic. -/
theorem localPathGraph_isAcyclic (n : ℕ) : (localPathGraph n).IsAcyclic := by
  intro v c hcycle
  -- Since c is a cycle it is non-nil; write c = cons hadj q
  cases c with
  | nil =>
    -- nil cannot be a cycle
    exact hcycle.ne_nil rfl
  | cons hadj q =>
    -- hadj : (localPathGraph n).Adj v w  for the first step
    -- q    : (localPathGraph n).Walk w v  for the rest
    -- From cons_isCycle_iff: q is a path and {v,w} ∉ q.edges
    rw [Walk.cons_isCycle_iff] at hcycle
    obtain ⟨hpath, hedge⟩ := hcycle
    -- q.support.Nodup (from path condition)
    have hnodup : q.support.Nodup := hpath.support_nodup
    -- Inspect the LAST step of q by case-splitting on q.reverse
    -- q.reverse : Walk v w
    cases h_qr : q.reverse with
    | nil =>
      -- q.reverse = nil  ⟹  w ≐ v (definitional), so Adj v v — contradicts loopless
      exact (localPathGraph n).loopless v hadj
    | cons hadj_last r =>
      -- hadj_last : (localPathGraph n).Adj v z   (last step of q, reversed)
      -- r         : (localPathGraph n).Walk z w
      -- h_qr      : q.reverse = Walk.cons hadj_last r

      -- The last edge of q is s(v, z)
      have hedge_last : s(v, z) ∈ q.edges := by
        have h1 : s(v, z) ∈ q.reverse.edges := by
          rw [h_qr, Walk.edges_cons]
          exact List.mem_cons_self _ _
        rwa [Walk.edges_reverse, List.mem_reverse] at h1

      -- z ≠ w: if z = w then s(v,z) = s(v,w) ∈ q.edges contradicts hedge
      have hz_ne_w : z ≠ w := fun heq ↦ by subst heq; exact hedge hedge_last

      -- Key structural fact: q.support.reverse = v :: r.support
      have hsupp_rev : q.support.reverse = v :: r.support := by
        have := (Walk.support_reverse q).symm
        rw [h_qr, Walk.support_cons] at this
        exact this

      -- Therefore v ∉ r.support  (Nodup prevents a second occurrence of v)
      have hv_not_in_r : v ∉ r.support := by
        have hnd : (v :: r.support).Nodup := by
          rwa [← hsupp_rev, List.nodup_reverse]
        exact (List.nodup_cons.mp hnd).1

      -- Adjacency values for the first and last steps
      have hw_vals : v.val + 1 = w.val ∨ w.val + 1 = v.val := hadj
      have hz_vals : v.val + 1 = z.val ∨ z.val + 1 = v.val := hadj_last

      -- Four sub-cases; two are immediately contradictory (z = w), two need IVT
      rcases hw_vals with hw | hw <;> rcases hz_vals with hz | hz
      · -- First step right (w = v+1), last step also right (z = v+1 = w) → z = w
        exact hz_ne_w (Fin.ext (by omega))
      · -- First step right (w = v+1), last step left (z = v−1)
        -- IVT on r.reverse : Walk w z,  z.val < v.val < w.val
        obtain ⟨u, hu_in_rev, hu_val⟩ :=
          localPathGraph_walk_ivt r.reverse (by omega : z.val < v.val) (by omega : v.val < w.val)
        rw [Walk.support_reverse, List.mem_reverse] at hu_in_rev
        exact hv_not_in_r (Fin.ext hu_val ▸ hu_in_rev)
      · -- First step left (w = v−1), last step right (z = v+1)
        -- IVT directly on r : Walk z w,  w.val < v.val < z.val
        obtain ⟨u, hu_in_r, hu_val⟩ :=
          localPathGraph_walk_ivt r (by omega : w.val < v.val) (by omega : v.val < z.val)
        exact hv_not_in_r (Fin.ext hu_val ▸ hu_in_r)
      · -- First step left (w = v−1), last step also left (z = v−1 = w) → z = w
        exact hz_ne_w (Fin.ext (by omega))

end PNP

/-!
## Infinite path graph on ℕ

The same argument works for the infinite path graph on ℕ.
Used by `TreewidthCombinatorial.lean`.
-/

namespace NatPath

open SimpleGraph Walk

/-- The infinite path graph on ℕ: vertex i is adjacent to i ± 1. -/
def natPathGraph : SimpleGraph ℕ where
  Adj i j := (i + 1 = j) ∨ (j + 1 = i)
  symm    := fun _ _ h ↦ h.symm
  loopless := fun _ h ↦ by rcases h with h | h <;> omega

/-- Discrete IVT for the infinite path graph (downward direction). -/
private lemma natPathGraph_walk_ivt
    {a b : ℕ} (q : natPathGraph.Walk a b)
    {k : ℕ} (hlo : b < k) (hhi : k < a) :
    ∃ u ∈ q.support, u = k := by
  induction q with
  | nil => exact absurd hhi (by omega)
  | @cons _ a c _ hadj r ih =>
    have hadj_vals : a + 1 = c ∨ c + 1 = a := hadj
    simp only [Walk.support_cons, List.mem_cons]
    rcases hadj_vals with h | h
    · obtain ⟨u, hu, huv⟩ := ih hlo (by omega : k < c)
      exact ⟨u, .inr hu, huv⟩
    · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hhi) with rfl | hlt
      · exact ⟨c, .inr (Walk.start_mem_support r), rfl⟩
      · obtain ⟨u, hu, huv⟩ := ih hlo hlt
        exact ⟨u, .inr hu, huv⟩

/-- The infinite path graph on ℕ is acyclic. -/
theorem natPathGraph_isAcyclic : natPathGraph.IsAcyclic := by
  intro v c hcycle
  cases c with
  | nil => exact hcycle.ne_nil rfl
  | cons hadj q =>
    rw [Walk.cons_isCycle_iff] at hcycle
    obtain ⟨hpath, hedge⟩ := hcycle
    have hnodup : q.support.Nodup := hpath.support_nodup
    cases h_qr : q.reverse with
    | nil => exact natPathGraph.loopless v hadj
    | cons hadj_last r =>
      have hedge_last : s(v, z) ∈ q.edges := by
        have h1 : s(v, z) ∈ q.reverse.edges := by
          rw [h_qr, Walk.edges_cons]; exact List.mem_cons_self _ _
        rwa [Walk.edges_reverse, List.mem_reverse] at h1
      have hz_ne_w : z ≠ w := fun heq ↦ by subst heq; exact hedge hedge_last
      have hsupp_rev : q.support.reverse = v :: r.support := by
        have := (Walk.support_reverse q).symm
        rw [h_qr, Walk.support_cons] at this; exact this
      have hv_not_in_r : v ∉ r.support := by
        have hnd : (v :: r.support).Nodup := by
          rwa [← hsupp_rev, List.nodup_reverse]
        exact (List.nodup_cons.mp hnd).1
      have hw_vals : v + 1 = w ∨ w + 1 = v := hadj
      have hz_vals : v + 1 = z ∨ z + 1 = v := hadj_last
      rcases hw_vals with hw | hw <;> rcases hz_vals with hz | hz
      · exact hz_ne_w (by omega)
      · obtain ⟨u, hu_rev, hu_val⟩ := natPathGraph_walk_ivt r.reverse (by omega) (by omega)
        rw [Walk.support_reverse, List.mem_reverse] at hu_rev
        exact hv_not_in_r (hu_val ▸ hu_rev)
      · obtain ⟨u, hu_r, hu_val⟩ := natPathGraph_walk_ivt r (by omega) (by omega)
        exact hv_not_in_r (hu_val ▸ hu_r)
      · exact hz_ne_w (by omega)

/--
**Connectivity of the infinite path graph on ℕ**.

Every pair of natural numbers is connected: go `u → u-1 → ... → 0 → 1 → ... → v`.
-/
theorem natPathGraph_connected : natPathGraph.Connected := by
  intro u v
  -- Key: every n is reachable from 0 by going 0 → 1 → ... → n
  have key : ∀ n : ℕ, natPathGraph.Reachable 0 n := by
    intro n
    induction n with
    | zero => exact Walk.nil.reachable
    | succ k ih =>
      -- Append one more step: k → k+1
      -- natPathGraph.Adj k (k+1) holds by the left disjunct: k+1 = k+1
      have hadj : natPathGraph.Adj k (k + 1) := Or.inl rfl
      exact ih.trans (Walk.nil.cons hadj).reachable
  -- Reachable u v: go 0 ←(sym) u, then 0 → v
  exact (key u).symm.trans (key v)

/-- The infinite path graph on ℕ is a tree (connected and acyclic). -/
theorem natPathGraph_isTree : natPathGraph.IsTree :=
  ⟨natPathGraph_connected, natPathGraph_isAcyclic⟩

end NatPath
