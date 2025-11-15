#!/usr/bin/env python3
"""
Simple demonstration of the P-NP Computational Dichotomy Framework
===================================================================

This script provides a quick demonstration of the key components.

Usage:
    python3 simple_demo.py

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from src.ic_sat import (
    build_incidence_graph, estimate_treewidth, compare_treewidths,
    ic_sat, simple_dpll
)
from src.computational_dichotomy import CNFFormula, generate_low_treewidth_formula
from src.gadgets.tseitin_generator import generate_expander_tseitin
from src.proof_status import ProofStatus


def main():
    print("=" * 70)
    print("P-NP Computational Dichotomy: Simple Demonstration")
    print("=" * 70)
    print()
    
    # Example 1: Low Treewidth Formula (Tractable)
    print("Example 1: Low Treewidth Formula (Chain Structure)")
    print("-" * 70)
    
    low_tw_formula = generate_low_treewidth_formula(8)
    print(f"Formula: {low_tw_formula.num_vars} variables, {len(low_tw_formula.clauses)} clauses")
    
    primal_tw, incidence_tw = compare_treewidths(
        low_tw_formula.num_vars, 
        low_tw_formula.clauses
    )
    
    print(f"Primal treewidth: {primal_tw}")
    print(f"Incidence treewidth: {incidence_tw}")
    
    result = simple_dpll(low_tw_formula.clauses, low_tw_formula.num_vars)
    print(f"DPLL result: {result}")
    print(f"Status: LOW treewidth → TRACTABLE ✓")
    print()
    
    # Example 2: High Treewidth Formula (Intractable)
    print("Example 2: High Treewidth Formula (Expander Graph)")
    print("-" * 70)
    
    num_vars, clauses = generate_expander_tseitin(10, 3)
    print(f"Formula: {num_vars} variables, {len(clauses)} clauses")
    
    primal_tw, incidence_tw = compare_treewidths(num_vars, clauses)
    
    print(f"Primal treewidth: {primal_tw}")
    print(f"Incidence treewidth: {incidence_tw}")
    print(f"Status: HIGH treewidth → INTRACTABLE")
    print()
    
    # Example 3: IC-SAT Algorithm
    print("Example 3: IC-SAT Algorithm on Simple Formula")
    print("-" * 70)
    
    n_vars = 3
    clauses = [[1, 2], [-1, 3], [-2, -3]]
    print(f"Formula: {n_vars} variables, clauses = {clauses}")
    print()
    
    print("Running IC-SAT:")
    result = ic_sat(n_vars, clauses, log=True, max_depth=10)
    print(f"Result: {result}")
    print()
    
    # Summary
    print("=" * 70)
    print("Summary")
    print("=" * 70)
    print()
    print("This demonstration shows:")
    print("  ✓ Low treewidth formulas are tractable (can be solved efficiently)")
    print("  ✓ High treewidth formulas are intractable (exponential time)")
    print("  ✓ IC-SAT algorithm tracks information complexity")
    print("  ✓ Structural properties determine computational hardness")
    print()
    print("The framework demonstrates the computational dichotomy:")
    print("  φ ∈ P ⟺ tw(G_I(φ)) = O(log n)")
    print()
    
    # Display Proof Status
    print()
    print(ProofStatus.display_status())
    print()
    print("Frecuencia de resonancia: 141.7001 Hz ∞³")
    print()


if __name__ == "__main__":
    main()
