#!/usr/bin/env python3
"""
Hard Instance Generator for P≠NP Validation
Generates computationally hard SAT instances with high treewidth
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import networkx as nx
from src.gadgets.tseitin_generator import TseitinGenerator, generate_expander_tseitin
from src.ic_sat import estimate_treewidth, build_incidence_graph


def generate_hard_instance(n: int, seed: int = 42) -> tuple:
    """
    Generate a hard SAT instance with high treewidth.
    
    Args:
        n: Number of nodes in the base graph
        seed: Random seed for reproducibility
        
    Returns:
        Tuple of (clauses, graph, treewidth_estimate)
    """
    # Set random seed
    import random
    random.seed(seed)
    
    # Generate an expander graph which has high treewidth
    G = nx.random_regular_graph(3, n, seed=seed)
    
    # Generate Tseitin formula
    charge_assignment = [1] * n  # All odd charges for unsatisfiable formula
    generator = TseitinGenerator(G)
    num_vars, clauses = generator.generate_formula(charge_assignment)
    
    # Build incidence graph and estimate treewidth
    inc_graph = build_incidence_graph(num_vars, clauses)
    tw_estimate = estimate_treewidth(inc_graph)
    
    return clauses, G, tw_estimate


def generate_instance_suite(n_min: int = 10, n_max: int = 100, n_step: int = 10):
    """Generate a suite of hard instances for validation."""
    print("Generating Hard Instance Suite")
    print("=" * 50)
    
    instances = []
    
    for n in range(n_min, n_max + 1, n_step):
        clauses, graph, tw = generate_hard_instance(n)
        instances.append({
            'n': n,
            'num_clauses': len(clauses),
            'num_variables': len(set(abs(lit) for clause in clauses for lit in clause)),
            'treewidth_estimate': tw,
            'graph_nodes': graph.number_of_nodes(),
            'graph_edges': graph.number_of_edges()
        })
        
        print(f"n={n:3d}: {len(clauses):4d} clauses, tw≈{tw:.2f}")
    
    print(f"\nGenerated {len(instances)} hard instances")
    return instances


if __name__ == "__main__":
    print("Hard Instance Generator for P≠NP Proof Validation")
    print("=" * 60)
    print()
    
    # Generate instances
    instances = generate_instance_suite(10, 100, 10)
    
    print()
    print("Summary Statistics:")
    print(f"  Total instances: {len(instances)}")
    print(f"  Size range: {instances[0]['n']} to {instances[-1]['n']}")
    print(f"  Treewidth range: {min(i['treewidth_estimate'] for i in instances):.2f} to {max(i['treewidth_estimate'] for i in instances):.2f}")
    print()
    print("✅ Hard instance generation complete!")
