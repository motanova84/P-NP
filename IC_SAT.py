#!/usr/bin/env python3
"""
IC_SAT.py - Structural SAT solver with treewidth constraints

This is a wrapper/alias for the main IC-SAT implementation.
The actual implementation is in src/ic_sat.py
"""

import sys
import os
import argparse

# Add src directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

# Import the main IC-SAT module
from ic_sat import ic_sat, compare_treewidths, LargeScaleValidation


def main():
    """Main entry point for IC-SAT solver."""
    parser = argparse.ArgumentParser(
        description='IC-SAT: Structural SAT solver with treewidth constraints'
    )
    parser.add_argument(
        '--n',
        type=int,
        default=10,
        help='Number of variables for random 3-SAT instance (default: 10)'
    )
    parser.add_argument(
        '--clauses',
        type=int,
        help='Number of clauses (default: 4.3*n for critical region)'
    )
    parser.add_argument(
        '--log',
        action='store_true',
        help='Enable detailed logging'
    )
    
    args = parser.parse_args()
    
    print("IC-SAT Algorithm and Validation Framework ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print(f"Universal constant κ_Π: 2.5773")
    print()
    
    # Generate 3-SAT instance
    print(f"Generating 3-SAT instance with n={args.n} variables")
    print("-" * 70)
    
    validator = LargeScaleValidation()
    n_vars, clauses = validator.generate_3sat_critical(args.n)
    
    print(f"Generated 3-SAT with {n_vars} variables and {len(clauses)} clauses")
    print()
    
    # Compare treewidths
    print("Computing treewidth bounds...")
    primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
    print(f"  Primal graph treewidth:    {primal_tw}")
    print(f"  Incidence graph treewidth: {incidence_tw}")
    print()
    
    # Run IC-SAT
    print("Running IC-SAT solver...")
    result = ic_sat(n_vars, clauses, log=args.log)
    print(f"\nIC-SAT result: {'SATISFIABLE' if result else 'UNSATISFIABLE'}")
    print("-" * 70)
    print("\n✅ Validation complete")


if __name__ == '__main__':
    main()
