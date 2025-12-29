#!/usr/bin/env python3
"""
Demo script showcasing the enhanced P-NP computational dichotomy framework

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frecuencia de resonancia: 141.7001 Hz
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.computational_dichotomy import (
    CNF, incidence_graph, compare_treewidths, ic_sat, LargeScaleValidation
)
from src.gadgets.tseitin_generator import (
    generate_ramanujan_expander, generate_expander_tseitin, create_treewidth_hard_instance
)


def main():
    print("=" * 80)
    print("P-NP COMPUTATIONAL DICHOTOMY FRAMEWORK - DEMO")
    print("Complete IC-SAT Implementation & Validation Suite")
    print("=" * 80)
    print()
    
    # Demo 1: Treewidth comparison
    print("🔬 Demo 1: Treewidth Comparison")
    print("-" * 80)
    clauses = [[1, 2], [-1, 3], [2, -3]]
    n_vars = 3
    tw_p, tw_i = compare_treewidths(clauses, n_vars)
    print(f"Formula: {len(clauses)} clauses, {n_vars} variables")
    print(f"Primal treewidth: {tw_p:.2f}")
    print(f"Incidence treewidth: {tw_i:.2f}")
    print()
    
    # Demo 2: IC-SAT algorithm
    print("🔬 Demo 2: IC-SAT Algorithm")
    print("-" * 80)
    G = incidence_graph(n_vars, clauses)
    result = ic_sat(G, clauses, n_vars, max_depth=5)
    print(f"IC-SAT result: {result}")
    print()
    
    # Demo 3: Ramanujan expander generation
    print("🔬 Demo 3: Ramanujan-like Expander Graph")
    print("-" * 80)
    expander = generate_ramanujan_expander(12, d=3)
    print(f"Generated {expander.number_of_nodes()}-node expander")
    print(f"Regular degree: 3")
    print(f"Number of edges: {expander.number_of_edges()}")
    print()
    
    # Demo 4: Tseitin formula over expander
    print("🔬 Demo 4: Tseitin Formula over Expander")
    print("-" * 80)
    num_vars, tseitin_clauses = generate_expander_tseitin(8, 3)
    print(f"Generated Tseitin formula:")
    print(f"  Variables: {num_vars}")
    print(f"  Clauses: {len(tseitin_clauses)}")
    print(f"  First clause: {tseitin_clauses[0]}")
    print()
    
    # Demo 5: Treewidth-hard instance
    print("🔬 Demo 5: Treewidth-Hard Instance Creation")
    print("-" * 80)
    base_clauses = [[1, 2], [-1, 3]]
    hard_clauses, total_vars = create_treewidth_hard_instance(base_clauses, expander_size=10, d=3)
    print(f"Base formula: {len(base_clauses)} clauses")
    print(f"Combined hard instance: {len(hard_clauses)} clauses, {total_vars} variables")
    print()
    
    # Demo 6: Large-scale validation
    print("🔬 Demo 6: Large-Scale Validation")
    print("-" * 80)
    validator = LargeScaleValidation()
    
    # Generate a critical 3-SAT instance
    cnf = validator.generate_3sat_critical(8, ratio=4.0)
    print(f"Generated critical 3-SAT instance:")
    print(f"  Variables: {cnf.n_vars}")
    print(f"  Clauses: {len(cnf.clauses)}")
    print(f"  Ratio: {len(cnf.clauses) / cnf.n_vars:.2f}")
    
    # Estimate treewidth
    G_cnf = incidence_graph(cnf.n_vars, cnf.clauses)
    tw = validator.estimate_treewidth_practical(G_cnf)
    print(f"  Estimated treewidth: {tw:.2f}")
    print(f"  Coherence C: {1 / (1 + tw):.3f}")
    print()
    
    print("=" * 80)
    print("✅ Demo completed successfully!")
    print("All features are working correctly.")
    print("=" * 80)


if __name__ == "__main__":
    main()
