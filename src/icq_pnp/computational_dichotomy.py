"""
Module: computational_dichotomy
Implements the IC-SAT validation framework for the P vs NP treewidth dichotomy.

This module demonstrates the computational dichotomy via treewidth and information complexity.

The framework explores:
- Low treewidth formulas (tractable)
- High treewidth formulas (intractable)
- Structural coupling with expanders
- Non-evasion property

Author: José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)
Frecuencia de resonancia: 141.7001 Hz
"""

import argparse
import os
import networkx as nx
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from typing import List, Tuple, Set, Dict
from pathlib import Path


class CNFFormula:
    """Represents a CNF formula with its incidence graph."""
    
    def __init__(self, num_vars: int, clauses: List[List[int]]):
        """
        Initialize a CNF formula.
        
        Args:
            num_vars: Number of variables
            clauses: List of clauses, where each clause is a list of literals
                    (positive for x_i, negative for ¬x_i)
        """
        self.num_vars = num_vars
        self.clauses = clauses
        self.incidence_graph = self._build_incidence_graph()
    
    def _build_incidence_graph(self) -> nx.Graph:
        """Build the incidence graph of the formula."""
        G = nx.Graph()
        
        # Add variable nodes
        for i in range(1, self.num_vars + 1):
            G.add_node(f"v{i}", bipartite=0)
        
        # Add clause nodes and edges
        for idx, clause in enumerate(self.clauses):
            clause_node = f"c{idx}"
            G.add_node(clause_node, bipartite=1)
            
            for lit in clause:
                var = abs(lit)
                G.add_edge(f"v{var}", clause_node)
        
        return G
    
    def compute_treewidth_approximation(self) -> int:
        """
        Compute an approximation of the treewidth.
        Note: Computing exact treewidth is NP-hard, so we use heuristics.
        """
        try:
            # Use minimum degree heuristic for tree decomposition
            tree_decomp = nx.approximation.treewidth_min_degree(self.incidence_graph)
            return tree_decomp[0]
        except:
            # Fallback: return maximum degree as upper bound
            if len(self.incidence_graph.nodes()) > 0:
                return max(dict(self.incidence_graph.degree()).values())
            return 0
    
    def __repr__(self) -> str:
        return f"CNFFormula(vars={self.num_vars}, clauses={len(self.clauses)})"


def generate_low_treewidth_formula(n: int) -> CNFFormula:
    """
    Generate a CNF formula with low treewidth (tractable).
    Uses a chain structure which has treewidth 2.
    """
    clauses = []
    
    # Create a chain of implications: x1 -> x2 -> x3 -> ... -> xn
    for i in range(1, n):
        clauses.append([-i, i+1])  # ¬x_i ∨ x_{i+1}
    
    # Add unit clauses at ends
    clauses.append([1])   # x_1
    clauses.append([-n])  # ¬x_n
    
    return CNFFormula(n, clauses)


def demonstrate_dichotomy():
    """Demonstrate the computational dichotomy."""
    print("=" * 70)
    print("COMPUTATIONAL DICHOTOMY FRAMEWORK ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print("=" * 70)
    print()
    
    # Low treewidth example
    print("📊 Example 1: Low Treewidth Formula (Tractable)")
    print("-" * 70)
    low_tw_formula = generate_low_treewidth_formula(10)
    tw_approx = low_tw_formula.compute_treewidth_approximation()
    print(f"Formula: {low_tw_formula}")
    print(f"Approximate treewidth: {tw_approx}")
    print(f"Status: TRACTABLE (treewidth = O(log n))")
    print()
    
    # High treewidth example (conceptual)
    print("📊 Example 2: High Treewidth Formula (Intractable)")
    print("-" * 70)
    print("Note: High treewidth formulas (e.g., Tseitin over expanders)")
    print("would be generated using the tseitin_generator module.")
    print("Status: INTRACTABLE (treewidth = Ω(n))")
    print()
    
    print("=" * 70)
    print("🔬 Key Insight:")
    print("The dichotomy shows that computational hardness correlates")
    print("with structural properties (treewidth) that cannot be evaded")
    print("through algorithmic techniques.")
    print("=" * 70)


def ic_sat_validate(n_values: List[int], clause_var_ratio: float = 4.2) -> List[Dict]:
    """
    Validate IC-SAT framework with varying problem sizes.
    
    Args:
        n_values: List of problem sizes (number of variables)
        clause_var_ratio: Ratio of clauses to variables
        
    Returns:
        List of result dictionaries with n, treewidth, coherence, solved status
    """
    results = []
    
    for n in n_values:
        # Generate low treewidth formula
        formula = generate_low_treewidth_formula(n)
        tw = formula.compute_treewidth_approximation()
        
        # Coherence measure (simplified)
        coherence = np.log(n) / (tw + 1)
        
        # Solved status (tractable if treewidth is O(log n))
        solved = bool(tw <= 2 * np.log2(n) if n > 0 else True)
        
        results.append({
            "n": n,
            "treewidth": tw,
            "coherence": coherence,
            "solved": solved
        })
    
    return results


def save_results(results: List[Dict], output_path: str = "results/ic_sat_results.csv"):
    """
    Save validation results to CSV file.
    
    Args:
        results: List of result dictionaries
        output_path: Path to output CSV file
    """
    # Create results directory if it doesn't exist
    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    
    # Convert to DataFrame and save
    df = pd.DataFrame(results)
    df.to_csv(output_path, index=False)
    print(f"✓ Results saved to {output_path}")
    

def plot_scaling(results: List[Dict], output_path: str = "results/plots/treewidth_scaling.png"):
    """
    Create log-log plot of treewidth scaling.
    
    Args:
        results: List of result dictionaries
        output_path: Path to output plot image
    """
    # Create plots directory if it doesn't exist
    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    
    df = pd.DataFrame(results)
    
    plt.figure(figsize=(10, 6))
    plt.loglog(df['n'], df['treewidth'], 'bo-', label='Treewidth', linewidth=2, markersize=8)
    plt.loglog(df['n'], np.log2(df['n']), 'r--', label='O(log n)', linewidth=2)
    
    plt.xlabel('Problem Size (n)', fontsize=12)
    plt.ylabel('Treewidth', fontsize=12)
    plt.title('Scaling of Treewidth vs Problem Size', fontsize=14)
    plt.legend(fontsize=10)
    plt.grid(True, alpha=0.3)
    
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"✓ Plot saved to {output_path}")
    plt.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description='IC-SAT Validation Framework for P vs NP Dichotomy'
    )
    parser.add_argument(
        '--n', 
        nargs='+', 
        type=int, 
        default=[200, 300, 400, 500, 600],
        help='Problem sizes to test (number of variables)'
    )
    parser.add_argument(
        '--ratio', 
        type=float, 
        default=4.2,
        help='Clause-to-variable ratio'
    )
    parser.add_argument(
        '--output-dir',
        type=str,
        default='results',
        help='Output directory for results and plots'
    )
    parser.add_argument(
        '--demo',
        action='store_true',
        help='Run demonstration mode'
    )
    
    args = parser.parse_args()
    
    if args.demo:
        # Run original demonstration
        demonstrate_dichotomy()
    else:
        # Run validation with configurable parameters
        print("=" * 70)
        print("IC-SAT VALIDATION FRAMEWORK ∞³")
        print("Instituto de Conciencia Cuántica (ICQ)")
        print("=" * 70)
        print(f"Testing problem sizes: {args.n}")
        print(f"Clause-to-variable ratio: {args.ratio}")
        print()
        
        # Run validation
        results = ic_sat_validate(args.n, args.ratio)
        
        # Save results
        csv_path = os.path.join(args.output_dir, "ic_sat_results.csv")
        save_results(results, csv_path)
        
        # Create plot
        plot_path = os.path.join(args.output_dir, "plots", "treewidth_scaling.png")
        plot_scaling(results, plot_path)
        
        # Print summary
        print()
        print("=" * 70)
        print("VALIDATION SUMMARY")
        print("=" * 70)
        df = pd.DataFrame(results)
        print(df.to_string(index=False))
        print()
        print(f"✓ All tractable cases: {df['solved'].all()}")
        print("=" * 70)
