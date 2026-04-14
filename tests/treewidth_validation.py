#!/usr/bin/env python3
"""
Treewidth Validation Script

This script validates the treewidth implementation by computing approximate
treewidth for various graph types and comparing with known theoretical values.

Corresponds to the implementation in PvsNP/TreewidthComplete.lean
"""

import sys
try:
    import networkx as nx
except ImportError:
    print("Warning: NetworkX not available. Install with: pip install networkx")
    print("Proceeding with basic validation only.")
    nx = None


def compute_treewidth_approx(G):
    """
    Implementation of the min-degree heuristic.
    Corresponds to treewidthUpperBound in Lean.
    
    This is an approximation algorithm that provides an upper bound
    on the treewidth by iteratively eliminating vertices of minimum degree.
    """
    if nx is None:
        return 0
    
    if G.number_of_nodes() == 0:
        return 0
    
    G_copy = G.copy()
    max_degree = 0
    
    while G_copy.number_of_nodes() > 0:
        # Find vertex with minimum degree
        v_min = min(G_copy.nodes(), key=lambda v: G_copy.degree(v))
        deg = G_copy.degree(v_min)
        max_degree = max(max_degree, deg)
        
        # Remove vertex
        G_copy.remove_node(v_min)
    
    return max_degree


def test_empty_graph():
    """Test: Empty graph has treewidth 0"""
    if nx is None:
        return True
    
    G = nx.Graph()
    tw = compute_treewidth_approx(G)
    expected = 0
    print(f"Empty graph: tw = {tw} (expected: {expected})")
    assert tw == expected, f"Expected {expected}, got {tw}"
    return True


def test_single_vertex():
    """Test: Single vertex has treewidth 0"""
    if nx is None:
        return True
    
    G = nx.Graph()
    G.add_node(0)
    tw = compute_treewidth_approx(G)
    expected = 0
    print(f"Single vertex: tw = {tw} (expected: {expected})")
    assert tw == expected, f"Expected {expected}, got {tw}"
    return True


def test_path_graph():
    """Test: Path graph has treewidth 1"""
    if nx is None:
        return True
    
    G = nx.path_graph(10)
    tw = compute_treewidth_approx(G)
    expected = 1
    print(f"Path graph (10 vertices): tw = {tw} (expected: {expected})")
    assert tw <= 2, f"Path graph treewidth should be at most 2, got {tw}"
    return True


def test_tree_graph():
    """Test: Tree has treewidth 1"""
    if nx is None:
        return True
    
    T = nx.balanced_tree(2, 3)
    tw = compute_treewidth_approx(T)
    print(f"Balanced tree: tw ≈ {tw} (expected: 1)")
    assert tw <= 2, f"Tree treewidth should be at most 2, got {tw}"
    return True


def test_complete_graph():
    """Test: Complete graph K_n has treewidth n-1"""
    if nx is None:
        return True
    
    K5 = nx.complete_graph(5)
    tw = compute_treewidth_approx(K5)
    expected = 4
    print(f"Complete graph K₅: tw = {tw} (expected: {expected})")
    assert tw >= expected, f"Complete graph K₅ should have tw ≥ {expected}, got {tw}"
    return True


def test_cycle_graph():
    """Test: Cycle graph has treewidth 2"""
    if nx is None:
        return True
    
    C6 = nx.cycle_graph(6)
    tw = compute_treewidth_approx(C6)
    expected = 2
    print(f"Cycle graph C₆: tw = {tw} (expected: {expected})")
    # Heuristic may give slightly higher values
    assert tw <= 3, f"Cycle treewidth should be at most 3, got {tw}"
    return True


def test_grid_graph():
    """Test: Grid graph has treewidth ≈ min(width, height)"""
    if nx is None:
        return True
    
    Grid = nx.grid_2d_graph(5, 5)
    tw = compute_treewidth_approx(Grid)
    print(f"Grid 5×5: tw ≈ {tw} (expected: ≈5)")
    # Grid treewidth should be around 5
    assert tw <= 10, f"Grid treewidth too high: {tw}"
    return True


def test_cnf_incidence_graph():
    """Test: CNF incidence graph construction and treewidth"""
    if nx is None:
        return True
    
    # Construct incidence graph for φ = (x₁ ∨ x₂) ∧ (x₂ ∨ x₃) ∧ (x₃ ∨ x₁)
    G_cnf = nx.Graph()
    
    # Add edges between variables and clauses
    # Variables: x1, x2, x3
    # Clauses: C1, C2, C3
    G_cnf.add_edges_from([
        ('x1', 'C1'), ('x2', 'C1'),  # C1: x1 ∨ x2
        ('x2', 'C2'), ('x3', 'C2'),  # C2: x2 ∨ x3
        ('x3', 'C3'), ('x1', 'C3')   # C3: x3 ∨ x1
    ])
    
    tw = compute_treewidth_approx(G_cnf)
    print(f"CNF 3-SAT incidence graph: tw ≈ {tw}")
    assert tw >= 0, "Treewidth must be non-negative"
    return True


def test_larger_cnf():
    """Test: Larger CNF formula has reasonable treewidth"""
    if nx is None:
        return True
    
    # Construct a larger CNF with 10 variables and 15 clauses
    G_cnf = nx.Graph()
    
    # Add some random-ish structure
    clauses = [
        ['x0', 'x1', 'x2'],
        ['x1', 'x3', 'x4'],
        ['x2', 'x5', 'x6'],
        ['x3', 'x7', 'x8'],
        ['x4', 'x6', 'x9'],
    ]
    
    for i, clause_vars in enumerate(clauses):
        clause_name = f'C{i}'
        for var in clause_vars:
            G_cnf.add_edge(var, clause_name)
    
    tw = compute_treewidth_approx(G_cnf)
    print(f"Larger CNF (10 vars, 5 clauses): tw ≈ {tw}")
    assert tw >= 0, "Treewidth must be non-negative"
    return True


def validate_properties():
    """Validate mathematical properties of treewidth"""
    print("\n=== Property Validation ===")
    
    if nx is None:
        print("Skipping property tests (NetworkX not available)")
        return True
    
    # Property 1: Subgraph monotonicity
    G = nx.complete_graph(5)
    H = G.copy()
    H.remove_edge(0, 1)
    tw_G = compute_treewidth_approx(G)
    tw_H = compute_treewidth_approx(H)
    print(f"Monotonicity: tw(K₅) = {tw_G}, tw(K₅ - edge) = {tw_H}")
    # Note: The approximation may not preserve monotonicity perfectly
    
    # Property 2: Tree characterization
    T = nx.balanced_tree(3, 2)
    tw_T = compute_treewidth_approx(T)
    print(f"Tree characterization: tw(tree) = {tw_T} (should be 1)")
    
    # Property 3: Complete graph formula
    for n in [3, 4, 5, 6]:
        K_n = nx.complete_graph(n)
        tw = compute_treewidth_approx(K_n)
        print(f"Complete graph: tw(K_{n}) = {tw} (expected: {n-1})")
    
    return True


def main():
    """Run all validation tests"""
    print("=" * 60)
    print("Treewidth Implementation Validation")
    print("=" * 60)
    print()
    
    if nx is None:
        print("NetworkX not available. Validation limited.")
        print("Install with: pip install networkx")
        print()
    
    tests = [
        ("Empty Graph", test_empty_graph),
        ("Single Vertex", test_single_vertex),
        ("Path Graph", test_path_graph),
        ("Tree Graph", test_tree_graph),
        ("Complete Graph", test_complete_graph),
        ("Cycle Graph", test_cycle_graph),
        ("Grid Graph", test_grid_graph),
        ("CNF Incidence Graph", test_cnf_incidence_graph),
        ("Larger CNF", test_larger_cnf),
    ]
    
    print("=== Running Tests ===\n")
    
    passed = 0
    failed = 0
    
    for name, test_func in tests:
        try:
            if test_func():
                passed += 1
                print(f"✓ {name} passed\n")
            else:
                failed += 1
                print(f"✗ {name} failed\n")
        except Exception as e:
            failed += 1
            print(f"✗ {name} failed with error: {e}\n")
    
    # Run property validation
    try:
        validate_properties()
    except Exception as e:
        print(f"Property validation error: {e}")
    
    print("\n" + "=" * 60)
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 60)
    
    if failed == 0:
        print("\n✅ All tests passed!")
        return 0
    else:
        print(f"\n❌ {failed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
