#!/usr/bin/env python3
"""
Hard Instance Generator
========================

Generates hard SAT instances for validation of the P≠NP proof framework.
Creates instances with high treewidth using Tseitin formulas over expander graphs.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import networkx as nx
import numpy as np
import json
from typing import List, Dict, Any
from src.gadgets.tseitin_generator import TseitinGenerator
from src.ic_sat import estimate_treewidth, build_incidence_graph


def generate_expander_graph(n: int, d: int = 3) -> nx.Graph:
    """
    Generate a d-regular expander graph using random regular graph.
    
    Args:
        n: Number of nodes
        d: Degree of each node
        
    Returns:
        NetworkX graph
    """
    try:
        G = nx.random_regular_graph(d, n, seed=42)
        return G
    except:
        # Fallback to cycle graph if random regular fails
        return nx.cycle_graph(n)


def generate_hard_instance(n_nodes: int, dataset_name: str) -> Dict[str, Any]:
    """
    Generate a single hard SAT instance.
    
    Args:
        n_nodes: Number of nodes in the underlying graph
        dataset_name: Name for this instance
        
    Returns:
        Dictionary with instance data
    """
    # Generate expander graph
    G = generate_expander_graph(n_nodes)
    
    # Create Tseitin formula with odd charge
    tseitin_gen = TseitinGenerator(G)
    charge = [1] + [0] * (n_nodes - 1)  # Single odd charge makes it unsatisfiable
    n_vars, clauses = tseitin_gen.generate_formula(charge)
    
    # Build incidence graph and estimate treewidth
    G_inc = build_incidence_graph(n_vars, clauses)
    tw = estimate_treewidth(G_inc)
    
    return {
        'name': dataset_name,
        'n_nodes': n_nodes,
        'n_vars': n_vars,
        'n_clauses': len(clauses),
        'treewidth_estimate': tw,
        'graph_type': 'expander',
        'satisfiable': False
    }


def main():
    """Generate dataset of hard instances."""
    print("=" * 70)
    print("HARD INSTANCE GENERATOR")
    print("=" * 70)
    print()
    
    # Generate instances of various sizes
    sizes = [20, 30, 40, 50, 60, 80, 100]
    instances = []
    
    print("Generating hard instances...")
    for size in sizes:
        print(f"  Generating instance with {size} nodes...", end=" ")
        instance = generate_hard_instance(size, f"expander_{size}")
        instances.append(instance)
        print(f"✓ (tw ≈ {instance['treewidth_estimate']}, {instance['n_vars']} vars, {instance['n_clauses']} clauses)")
    
    # Save to results directory
    os.makedirs('results', exist_ok=True)
    output_file = 'results/hard_instances.json'
    
    with open(output_file, 'w') as f:
        json.dump({
            'instances': instances,
            'total_count': len(instances),
            'size_range': [min(sizes), max(sizes)]
        }, f, indent=2)
    
    print()
    print(f"✅ Generated {len(instances)} hard instances")
    print(f"📁 Results saved to: {output_file}")
    print()
    
    # Print summary statistics
    print("Summary Statistics:")
    print(f"  • Instance count: {len(instances)}")
    print(f"  • Size range: {min(sizes)} - {max(sizes)} nodes")
    print(f"  • Variable count range: {min(i['n_vars'] for i in instances)} - {max(i['n_vars'] for i in instances)}")
    print(f"  • Treewidth range: {min(i['treewidth_estimate'] for i in instances)} - {max(i['treewidth_estimate'] for i in instances)}")
    print()


if __name__ == '__main__':
    main()
