#!/usr/bin/env python3
"""
Simple demonstration of the optimal separator algorithm.

Shows how to use the OptimalSeparatorFinder on a few example graphs.

Author: José Manuel Mota Burruezo Ψ ∞³ (Campo QCAL)
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import networkx as nx
from src.optimal_separator_algorithm import OptimalSeparatorFinder, KAPPA_PI


def demo_tree():
    """Demonstrate on a simple tree."""
    print("=" * 60)
    print("EXAMPLE 1: Path Graph (Tree)")
    print("=" * 60)
    
    G = nx.path_graph(10)
    print(f"Graph: Path with {len(G)} nodes")
    print(f"Expected: Low treewidth (tw=1)")
    print()
    
    finder = OptimalSeparatorFinder(G)
    separator, meta = finder.find_optimal_separator()
    
    print(f"Results:")
    print(f"  Case: {meta['case']}")
    print(f"  Treewidth estimate: {meta['treewidth_estimate']}")
    print(f"  Separator: {separator}")
    print(f"  Separator size: {len(separator)}")
    print(f"  Threshold κ_Π√n: {meta['threshold']:.2f}")
    
    # Verify
    verify = finder.verify_optimality(separator)
    print(f"  Balanced: {verify['is_balanced']}")
    print(f"  Meets bound: {verify['meets_bound']}")
    print()


def demo_grid():
    """Demonstrate on a grid graph."""
    print("=" * 60)
    print("EXAMPLE 2: Grid Graph 5×5")
    print("=" * 60)
    
    G = nx.grid_2d_graph(5, 5)
    G = nx.convert_node_labels_to_integers(G)
    print(f"Graph: Grid with {len(G)} nodes")
    print(f"Expected: Medium treewidth (tw≈5)")
    print()
    
    finder = OptimalSeparatorFinder(G)
    separator, meta = finder.find_optimal_separator()
    
    print(f"Results:")
    print(f"  Case: {meta['case']}")
    print(f"  Treewidth estimate: {meta['treewidth_estimate']}")
    print(f"  Separator size: {len(separator)}")
    print(f"  Threshold κ_Π√n: {meta['threshold']:.2f}")
    
    # Verify
    verify = finder.verify_optimality(separator)
    print(f"  Max component size: {verify['max_component_size']}")
    print(f"  Balance ratio: {verify['balance_ratio']:.3f}")
    print(f"  Meets bound: {verify['meets_bound']}")
    print()


def demo_complete():
    """Demonstrate on a complete graph."""
    print("=" * 60)
    print("EXAMPLE 3: Complete Graph K₁₅")
    print("=" * 60)
    
    G = nx.complete_graph(15)
    print(f"Graph: Complete graph with {len(G)} nodes")
    print(f"Expected: High treewidth (tw=14)")
    print()
    
    finder = OptimalSeparatorFinder(G)
    separator, meta = finder.find_optimal_separator()
    
    print(f"Results:")
    print(f"  Case: {meta['case']}")
    print(f"  Treewidth estimate: {meta['treewidth_estimate']}")
    print(f"  Separator size: {len(separator)}")
    print(f"  Threshold κ_Π√n: {meta['threshold']:.2f}")
    
    if 'is_expander' in meta:
        print(f"  Is expander: {meta['is_expander']}")
    
    # Verify
    verify = finder.verify_optimality(separator)
    print(f"  Meets bound: {verify['meets_bound']}")
    print()


def demo_custom():
    """Demonstrate on a custom graph."""
    print("=" * 60)
    print("EXAMPLE 4: Custom Graph")
    print("=" * 60)
    
    # Create a more interesting graph - a cycle with chords
    G = nx.Graph()
    n = 12
    
    # Add cycle
    for i in range(n):
        G.add_edge(i, (i+1) % n)
    
    # Add some chords
    for i in range(0, n, 3):
        G.add_edge(i, (i+6) % n)
    
    print(f"Graph: Cycle with chords, {len(G)} nodes, {G.number_of_edges()} edges")
    print()
    
    finder = OptimalSeparatorFinder(G)
    separator, meta = finder.find_optimal_separator()
    
    print(f"Results:")
    print(f"  Case: {meta['case']}")
    print(f"  Treewidth estimate: {meta['treewidth_estimate']}")
    print(f"  Separator: {separator}")
    print(f"  Separator size: {len(separator)}")
    
    # Verify
    verify = finder.verify_optimality(separator)
    print(f"  Balanced: {verify['is_balanced']}")
    print(f"  Max component: {verify['max_component_size']}")
    print(f"  Meets bound: {verify['meets_bound']}")
    print()


def main():
    """Run all demonstrations."""
    print()
    print("*" * 60)
    print("OPTIMAL SEPARATOR ALGORITHM - QUICK DEMO")
    print(f"Universal Constant: κ_Π = {KAPPA_PI}")
    print("*" * 60)
    print()
    
    demo_tree()
    demo_grid()
    demo_complete()
    demo_custom()
    
    print("=" * 60)
    print("DEMO COMPLETE")
    print("=" * 60)
    print()
    print("Key Insights:")
    print("  • Low treewidth graphs → small separators")
    print("  • High treewidth graphs → large separators (expanders)")
    print("  • Threshold determined by κ_Π = 2.5773")
    print()
    print("For more details, see:")
    print("  • formal/Treewidth/README_OPTIMAL_SEPARATOR.md")
    print("  • src/optimal_separator_algorithm.py")
    print("  • tests/test_optimal_separator.py")
    print()


if __name__ == "__main__":
    main()
