# Roadmap: Completing cycle_treewidth_two

## Current Status

✅ **Foundation Complete**
- Basic arithmetic lemmas work
- Graph structures defined (cycle, path)
- Edge expansion machinery in place
- 11+ complete proofs without sorry

🔄 **In Progress**
- Tree decomposition structure
- Full cycle treewidth proof

## The Target Theorem

```lean
theorem cycle_treewidth_two (n : ℕ) (hn : n ≥ 3) :
    (cycleGraph n).treewidth = 2
```

## What's Needed

### 1. Tree Decomposition Definition ✅ (Partial)

Already exists in `formal/Treewidth/Treewidth.lean`:

```lean
structure TreeDecomposition (G : SimpleGraph V) where
  T : SimpleGraph V
  X : V → Finset V
  T_tree : T.IsTree
  cover : ∀ v : V, ∃ t : V, v ∈ X t
  edge_covered : ∀ v w : V, G.Adj v w → ∃ t : V, v ∈ X t ∧ w ∈ X t
  connected_subtree : ...
```

**Status**: Defined but needs testing with concrete examples.

### 2. Width Function ✅ (Exists)

```lean
def width {G : SimpleGraph V} (D : TreeDecomposition G) : ℕ :=
  (Finset.univ.image (fun t => (D.X t).card)).sup id - 1
```

**Status**: Defined in existing code.

### 3. Cycle Graph Properties ✅ (Partial)

We have:
- ✅ `cycleGraph` definition
- ✅ `cycleGraph_symm` (symmetry)
- 🔄 `cycleGraph_connected` (needs proof)

### 4. Upper Bound: Constructive Proof

**Goal**: Prove there exists a tree decomposition of width ≤ 2.

**Strategy**: Explicit construction!

```lean
def cycle_decomposition (n : ℕ) (hn : 3 ≤ n) : 
    TreeDecomposition (cycleGraph n) := {
  T := pathGraph n  -- Use path as decomposition tree
  X := fun i => {i, (i + 1) % n, (i + 2) % n}  -- Each bag has 3 consecutive vertices
  T_tree := pathGraph_is_tree n (by omega)
  cover := by
    -- Every vertex i appears in bag i
    intro v
    use v
    simp
    -- Show v ∈ {v, (v + 1) % n, (v + 2) % n}
  edge_covered := by
    -- Every edge (i, i+1) is covered by bag i
    intros v w hadj
    -- Cycle edges are between consecutive vertices
    -- Both endpoints appear in appropriate bag
  connected_subtree := by
    -- Bags containing vertex v form connected subtree
    -- For cycle: vertex i appears in bags i-2, i-1, i (mod n)
    -- These form a path in the tree T
}

lemma cycle_decomposition_width_two (n : ℕ) (hn : 3 ≤ n) :
    width (cycle_decomposition n hn) = 2 := by
  unfold width cycle_decomposition
  -- Each bag has exactly 3 vertices
  -- Width = 3 - 1 = 2
```

**Status**: ⬜ Not yet implemented

**Required Steps**:
1. Prove `pathGraph_is_tree`
2. Verify coverage property
3. Verify edge coverage
4. Verify connected subtree property
5. Calculate width = 2

### 5. Lower Bound: Impossibility Proof

**Goal**: Prove no tree decomposition has width < 2.

**Strategy**: Contradiction

```lean
lemma cycle_needs_width_two (n : ℕ) (hn : 3 ≤ n) :
    ∀ D : TreeDecomposition (cycleGraph n), width D ≥ 2 := by
  intro D
  by_contra h_lt
  -- Assume width < 2, so width ≤ 1
  have width_le_one : width D ≤ 1 := by omega
  
  -- Width ≤ 1 means each bag has ≤ 2 vertices
  have bag_size : ∀ t, (D.X t).card ≤ 2 := by
    intro t
    -- From width_le_one and width definition
  
  -- Pick three consecutive vertices in cycle: 0, 1, 2
  let v0 : Fin n := 0
  let v1 : Fin n := 1
  let v2 : Fin n := 2
  
  -- All three edges exist in cycle
  have e01 : (cycleGraph n).Adj v0 v1 := by simp [cycleGraph]
  have e12 : (cycleGraph n).Adj v1 v2 := by simp [cycleGraph]
  have e20 : (cycleGraph n).Adj v2 v0 := by simp [cycleGraph]
  
  -- By edge_covered, there exist bags containing each edge
  obtain ⟨t01, h01⟩ := D.edge_covered v0 v1 e01
  obtain ⟨t12, h12⟩ := D.edge_covered v1 v2 e12
  obtain ⟨t20, h20⟩ := D.edge_covered v2 v0 e20
  
  -- Key insight: bag containing edge must have both endpoints
  -- But each bag has ≤ 2 vertices
  -- Can't fit all 3 vertices with their 3 edges in bags of size 2
  
  -- This requires subtree connectivity argument
  -- The bags form a tree, but cycle requires "circular" coverage
  -- Contradiction!
```

**Status**: ⬜ Not yet implemented

**Required Steps**:
1. Formalize contradiction setup
2. Use subtree connectivity properties
3. Show impossibility of covering triangle with size-2 bags

### 6. Combine for Exact Result

```lean
theorem cycle_treewidth_two (n : ℕ) (hn : n ≥ 3) :
    (cycleGraph n).treewidth = 2 := by
  -- Upper bound: width ≤ 2
  have upper : ∃ D, width D ≤ 2 := by
    use cycle_decomposition n hn
    exact Nat.le_of_eq (cycle_decomposition_width_two n hn)
  
  -- Lower bound: width ≥ 2
  have lower : ∀ D, width D ≥ 2 := by
    exact cycle_needs_width_two n hn
  
  -- Combine
  unfold treewidth
  -- Use definition and bounds to conclude
```

**Status**: ⬜ Not yet implemented

## Step-by-Step Implementation Plan

### Phase 1: Foundation (✅ COMPLETE)
- [x] Basic lemmas
- [x] Graph definitions
- [x] Edge expansion

### Phase 2: Tree Properties (🔄 IN PROGRESS)
- [ ] Prove `pathGraph_is_tree`
- [ ] Prove `cycleGraph_connected`
- [ ] Test tree decomposition structure

### Phase 3: Upper Bound (⬜ TODO)
- [ ] Construct `cycle_decomposition`
- [ ] Prove coverage properties
- [ ] Prove width = 2

### Phase 4: Lower Bound (⬜ TODO)
- [ ] Set up contradiction
- [ ] Use subtree connectivity
- [ ] Complete impossibility proof

### Phase 5: Final Theorem (⬜ TODO)
- [ ] Combine bounds
- [ ] Complete `cycle_treewidth_two`
- [ ] Add documentation
- [ ] Create tests

## Estimated Complexity

- **Phase 2**: ~50 lines, medium difficulty
- **Phase 3**: ~100 lines, high difficulty (constructive proof)
- **Phase 4**: ~150 lines, very high difficulty (impossibility)
- **Phase 5**: ~20 lines, low difficulty (if phases 3-4 done)

**Total**: ~300-400 lines of careful proof

## Next Immediate Steps

1. **Test Tree Decomposition**: Create a simple example
   ```lean
   def trivial_decomposition : TreeDecomposition (cycleGraph 3) := ...
   ```

2. **Prove Path is Tree**: Complete `pathGraph_is_tree`

3. **Small Cases First**: Prove for n=3 specifically
   ```lean
   theorem cycle3_treewidth_two : (cycleGraph 3).treewidth = 2
   ```

4. **Generalize**: Extend to all n ≥ 3

## Resources and References

- **Existing Code**: `formal/Treewidth/Treewidth.lean`
- **Mathlib**: `Mathlib.Combinatorics.SimpleGraph.*`
- **Theory**: Standard treewidth textbooks (Bodlaender, et al.)

## Success Criteria

✅ **Complete** when:
1. `cycle_treewidth_two` theorem has no `sorry`
2. All helper lemmas proven
3. Examples demonstrate correctness
4. Documentation explains construction

## Why This Matters

This theorem demonstrates:
- ✅ We can build complete, sorry-free proofs
- ✅ The incremental approach works
- ✅ Real mathematics can be formalized
- ✅ The foundation is solid for larger goals

Once complete, this serves as a template for:
- Other graph treewidth results
- More complex computational theorems
- The full P vs NP formalization

---

**Status**: Foundation complete, ready for Phase 2! 🚀
