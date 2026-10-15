#!/usr/bin/env python3
"""
IC-SAT Validation Demo
======================

Demonstrates the IC-SAT algorithm with:
1. DIMACS file parsing
2. Treewidth estimation (primal and incidence graphs)
3. Ramanujan graph calibration
4. Large-scale validation (n=200-400)
5. Information complexity analysis

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.ic_sat import (
    build_primal_graph, build_incidence_graph,
    compare_treewidths, ic_sat, simple_dpll,
    LargeScaleValidation, validate_ramanujan_calibration,
    parse_dimacs, predict_advantages
)


def demo_basic_ic_sat():
    """Demonstrate basic IC-SAT functionality."""
    print("\n" + "=" * 70)
    print("DEMO 1: Basic IC-SAT Algorithm")
    print("=" * 70)
    print()
    
    # Example formula: (x1 ∨ ¬x2) ∧ (¬x1 ∨ x2)
    n_vars = 2
    clauses = [[1, -2], [-1, 2]]
    
    print(f"Formula: {clauses}")
    print(f"Variables: {n_vars}")
    print()
    
    # Compare treewidths
    primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
    print(f"Primal graph treewidth: {primal_tw}")
    print(f"Incidence graph treewidth: {incidence_tw}")
    print()
    
    # Solve with IC-SAT
    print("Solving with IC-SAT...")
    result = ic_sat(n_vars, clauses, log=True)
    print(f"\nResult: {result}")
    print()


def demo_treewidth_analysis():
    """Demonstrate treewidth analysis on different formulas."""
    print("\n" + "=" * 70)
    print("DEMO 2: Treewidth Analysis")
    print("=" * 70)
    print()
    
    test_cases = [
        {
            'name': 'Simple 2-SAT',
            'n_vars': 3,
            'clauses': [[1, 2], [2, 3], [-1, -3]]
        },
        {
            'name': 'Random 3-SAT (small)',
            'n_vars': 10,
            'clauses': None  # Will generate
        },
        {
            'name': 'Chain formula',
            'n_vars': 5,
            'clauses': [[i, i+1] for i in range(1, 5)]
        }
    ]
    
    validator = LargeScaleValidation()
    
    for test_case in test_cases:
        print(f"Testing: {test_case['name']}")
        
        if test_case['clauses'] is None:
            # Generate random 3-SAT
            n_vars, clauses = validator.generate_3sat_critical(test_case['n_vars'])
        else:
            n_vars = test_case['n_vars']
            clauses = test_case['clauses']
        
        primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
        
        print(f"  Variables: {n_vars}, Clauses: {len(clauses)}")
        print(f"  Primal TW: {primal_tw}, Incidence TW: {incidence_tw}")
        
        # Predict best variable to branch on
        G = build_incidence_graph(n_vars, clauses)
        best_var = predict_advantages(G)
        print(f"  Best variable to branch on: {best_var}")
        print()


def demo_ramanujan_calibration():
    """Demonstrate Ramanujan graph calibration validation."""
    print("\n" + "=" * 70)
    print("DEMO 3: Ramanujan Graph Calibration")
    print("=" * 70)
    
    validate_ramanujan_calibration()


def demo_large_scale_validation():
    """Demonstrate large-scale validation framework."""
    print("\n" + "=" * 70)
    print("DEMO 4: Large-Scale Validation")
    print("=" * 70)
    print()
    
    validator = LargeScaleValidation()
    
    # Run validation with smaller sizes for demo
    print("Running validation with n=50, 100 (demo sizes)...")
    print("For full validation, use n=200, 300, 400")
    print()
    
    results = validator.run_large_scale(
        n_values=[50, 100],
        ratios=[4.0, 4.26]
    )
    
    # Summary statistics
    print("\n" + "=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    print()
    
    print(f"{'Configuration':<20} {'TW':<8} {'IC-SAT':<10} {'DPLL':<10} {'Reduction':<12} {'Coherence':<12}")
    print("-" * 70)
    
    for config, data in results.items():
        print(f"{config:<20} "
              f"{data['tw_estimated']:<8} "
              f"{data['ic_sat_branches']:<10} "
              f"{data['minisat_branches']:<10} "
              f"{data['branch_reduction']:<12} "
              f"{data['coherence_C']:<12.6f}")
    
    print()


def demo_solver_comparison():
    """Compare IC-SAT vs DPLL on various instances."""
    print("\n" + "=" * 70)
    print("DEMO 5: Solver Comparison (IC-SAT vs DPLL)")
    print("=" * 70)
    print()
    
    validator = LargeScaleValidation()
    
    # Generate instances of increasing difficulty
    sizes = [10, 20, 30]
    
    print(f"{'Size':<8} {'TW':<8} {'IC-SAT Result':<15} {'DPLL Result':<15}")
    print("-" * 70)
    
    for n in sizes:
        n_vars, clauses = validator.generate_3sat_critical(n)
        _, incidence_tw = compare_treewidths(n_vars, clauses)
        
        # Run both solvers
        ic_result, ic_branches = validator.run_ic_sat(n_vars, clauses)
        dpll_result, dpll_branches = validator.run_minisat(n_vars, clauses)
        
        print(f"{n:<8} {incidence_tw:<8} {ic_result:<15} {dpll_result:<15}")
    
    print()


def main():
    """Run all demos."""
    print("=" * 70)
    print("IC-SAT VALIDATION DEMONSTRATION ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print("=" * 70)
    
    # Run all demos
    demo_basic_ic_sat()
    demo_treewidth_analysis()
    demo_ramanujan_calibration()
    demo_solver_comparison()
    demo_large_scale_validation()
    
    print("\n" + "=" * 70)
    print("All demos completed successfully! ✓")
    print("=" * 70)
    print()
    print("For full large-scale validation (n=200-400), run:")
    print("  python3 -c 'from src.ic_sat import LargeScaleValidation; "
          "v = LargeScaleValidation(); v.run_large_scale([200, 300, 400])'")
    print()


if __name__ == "__main__":
    main()
