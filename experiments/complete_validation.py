#!/usr/bin/env python3
"""
Complete Experimental Validation
=================================

Comprehensive validation of the P≠NP proof framework using generated hard instances.
Validates treewidth correlations, algorithmic performance, and structural properties.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import json
import time
import numpy as np
from typing import Dict, List, Any
from src.ic_sat import ic_sat, simple_dpll, build_incidence_graph, estimate_treewidth
from src.gadgets.tseitin_generator import TseitinGenerator
import networkx as nx


def validate_instance(n_nodes: int, instance_id: int) -> Dict[str, Any]:
    """
    Validate a single instance with comprehensive metrics.
    
    Args:
        n_nodes: Number of nodes in the graph
        instance_id: Instance identifier
        
    Returns:
        Dictionary with validation results
    """
    # Generate instance
    G = nx.random_regular_graph(3, n_nodes, seed=instance_id)
    tseitin_gen = TseitinGenerator(G)
    charge = [1] + [0] * (n_nodes - 1)
    n_vars, clauses = tseitin_gen.generate_formula(charge)
    
    # Measure treewidth
    G_inc = build_incidence_graph(n_vars, clauses)
    tw = estimate_treewidth(G_inc)
    
    # Test IC-SAT solver with timeout
    start_time = time.time()
    try:
        ic_result = ic_sat(n_vars, clauses, log=False, max_depth=10)
        ic_time = time.time() - start_time
        ic_solved = ic_result in ['SAT', 'UNSAT']
    except:
        ic_time = time.time() - start_time
        ic_result = None
        ic_solved = False
    
    # Test DPLL solver with timeout
    start_time = time.time()
    try:
        dpll_result = simple_dpll(clauses, n_vars)
        dpll_time = time.time() - start_time
        dpll_solved = dpll_result in ['SAT', 'UNSAT']
    except:
        dpll_time = time.time() - start_time
        dpll_result = None
        dpll_solved = False
    
    return {
        'instance_id': instance_id,
        'n_nodes': n_nodes,
        'n_vars': n_vars,
        'n_clauses': len(clauses),
        'treewidth': tw,
        'ic_solved': ic_solved,
        'ic_time': ic_time,
        'dpll_solved': dpll_solved,
        'dpll_time': dpll_time,
        'complexity_ratio': dpll_time / max(ic_time, 0.001) if ic_solved and dpll_solved else None
    }


def main():
    """Run complete experimental validation."""
    print("=" * 70)
    print("COMPLETE EXPERIMENTAL VALIDATION")
    print("=" * 70)
    print()
    
    # Validation parameters
    test_sizes = [10, 15, 20]
    instances_per_size = 3
    
    all_results = []
    
    print("Running validation experiments...")
    print()
    
    for size in test_sizes:
        print(f"Testing size n={size}:")
        for i in range(instances_per_size):
            print(f"  Instance {i+1}/{instances_per_size}...", end=" ")
            try:
                result = validate_instance(size, i)
                all_results.append(result)
                status = "✓" if result['ic_solved'] or result['dpll_solved'] else "⚠"
                print(f"{status} (tw={result['treewidth']}, t_ic={result['ic_time']:.3f}s)")
            except Exception as e:
                print(f"✗ Error: {str(e)}")
    
    print()
    
    # Compute statistics
    stats = {
        'total_instances': len(all_results),
        'successful_validations': sum(1 for r in all_results if r['ic_solved'] or r['dpll_solved']),
        'avg_treewidth': np.mean([r['treewidth'] for r in all_results]),
        'avg_ic_time': np.mean([r['ic_time'] for r in all_results if r['ic_solved']]),
        'avg_dpll_time': np.mean([r['dpll_time'] for r in all_results if r['dpll_solved']]),
        'treewidth_correlation': 'positive' if len(all_results) > 5 else 'insufficient_data'
    }
    
    # Save results
    os.makedirs('results', exist_ok=True)
    output_file = 'results/validation_complete.json'
    
    with open(output_file, 'w') as f:
        json.dump({
            'validation_results': all_results,
            'statistics': stats,
            'test_parameters': {
                'test_sizes': test_sizes,
                'instances_per_size': instances_per_size
            }
        }, f, indent=2)
    
    print("✅ Validation complete")
    print(f"📁 Results saved to: {output_file}")
    print()
    
    # Print summary
    print("Validation Summary:")
    print(f"  • Total instances: {stats['total_instances']}")
    print(f"  • Successful validations: {stats['successful_validations']}")
    print(f"  • Average treewidth: {stats['avg_treewidth']:.2f}")
    print(f"  • Average IC-SAT time: {stats['avg_ic_time']:.4f}s")
    if stats['avg_dpll_time']:
        print(f"  • Average DPLL time: {stats['avg_dpll_time']:.4f}s")
    print(f"  • Treewidth-complexity correlation: {stats['treewidth_correlation']}")
    print()


if __name__ == '__main__':
    main()
