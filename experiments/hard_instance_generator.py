#!/usr/bin/env python3
"""
Hard Instance Generator for P≠NP Validation
============================================

Generates hard SAT instances with controlled treewidth properties
for validating the computational dichotomy theorem.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import networkx as nx
from typing import List, Tuple
from src.gadgets.tseitin_generator import TseitinGenerator


class HardInstanceGenerator:
    """Generator for hard SAT instances with specific treewidth properties"""
    
    def __init__(self, seed: int = 42):
        """
        Initialize generator
        
        Args:
            seed: Random seed for reproducibility
        """
        self.seed = seed
        np.random.seed(seed)
        self.tseitin_gen = TseitinGenerator()
    
    def generate_random_3sat(self, n: int, ratio: float = 4.3) -> List:
        """
        Generate random 3-SAT instance
        
        Args:
            n: Number of variables
            ratio: Clause-to-variable ratio (4.3 is near phase transition)
            
        Returns:
            List of clauses
        """
        m = int(n * ratio)
        clauses = []
        
        for _ in range(m):
            vars_in_clause = np.random.choice(range(1, n+1), size=3, replace=False)
            signs = np.random.choice([1, -1], size=3)
            clause = [int(v * s) for v, s in zip(vars_in_clause, signs)]
            clauses.append(clause)
        
        return clauses
    
    def generate_low_treewidth(self, n: int) -> Tuple[List, int]:
        """
        Generate SAT instance with low treewidth (O(log n))
        
        Uses path-like or tree-like structure
        
        Args:
            n: Number of variables
            
        Returns:
            (clauses, estimated_treewidth)
        """
        # Create path graph (treewidth = 1)
        G = nx.path_graph(n)
        
        # Generate Tseitin formula
        clauses = self.tseitin_gen.generate_tseitin_formula(G)
        tw = 1  # Path has treewidth 1
        
        return clauses, tw
    
    def generate_high_treewidth(self, n: int) -> Tuple[List, int]:
        """
        Generate SAT instance with high treewidth (ω(log n))
        
        Uses expander graphs (Ramanujan expanders ideally)
        
        Args:
            n: Number of variables
            
        Returns:
            (clauses, estimated_treewidth)
        """
        # Create regular expander (high treewidth)
        d = min(int(np.sqrt(n)), 10)  # Degree
        G = nx.random_regular_graph(d, n)
        
        # Generate Tseitin formula
        clauses = self.tseitin_gen.generate_tseitin_formula(G)
        
        # Estimate treewidth (expanders have linear treewidth)
        tw = self.tseitin_gen.estimate_treewidth(G)
        
        return clauses, tw
    
    def generate_controlled_treewidth(self, n: int, target_tw: int) -> Tuple[List, int]:
        """
        Generate SAT instance with approximately target treewidth
        
        Args:
            n: Number of variables
            target_tw: Target treewidth
            
        Returns:
            (clauses, actual_treewidth)
        """
        # Use grid graph with controlled dimensions
        # Grid graph has treewidth ≈ min(width, height)
        if target_tw <= 1:
            return self.generate_low_treewidth(n)
        
        # Create grid with target treewidth
        width = min(target_tw, int(np.sqrt(n)))
        height = n // width
        
        G = nx.grid_2d_graph(width, height)
        
        # Relabel nodes to integers
        mapping = {node: i for i, node in enumerate(G.nodes())}
        G = nx.relabel_nodes(G, mapping)
        
        # Generate Tseitin formula
        clauses = self.tseitin_gen.generate_tseitin_formula(G)
        tw = self.tseitin_gen.estimate_treewidth(G)
        
        return clauses, tw
    
    def generate_ramanujan_expander(self, n: int) -> Tuple[List, int]:
        """
        Generate Ramanujan expander (optimal expansion, high treewidth)
        
        Args:
            n: Number of vertices (should be prime^k + 1 ideally)
            
        Returns:
            (clauses, estimated_treewidth)
        """
        # For simplicity, use random regular graph as approximation
        # True Ramanujan expanders require more sophisticated construction
        d = min(int(np.log(n)), 10)  # Logarithmic degree
        G = nx.random_regular_graph(d, n)
        
        clauses = self.tseitin_gen.generate_tseitin_formula(G)
        tw = self.tseitin_gen.estimate_treewidth(G)
        
        return clauses, tw
    
    def save_instance_to_cnf(self, clauses: List, n: int, filename: str):
        """
        Save SAT instance in DIMACS CNF format
        
        Args:
            clauses: List of clauses
            n: Number of variables
            filename: Output filename
        """
        m = len(clauses)
        
        with open(filename, 'w') as f:
            f.write(f"p cnf {n} {m}\n")
            for clause in clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")
        
        print(f"✓ Saved instance to {filename}")


def main():
    """Main entry point for testing"""
    print("\n" + "="*70)
    print("HARD INSTANCE GENERATOR - P≠NP VALIDATION")
    print("="*70)
    
    gen = HardInstanceGenerator()
    
    # Generate examples
    print("\nGenerating example instances...")
    
    # Low treewidth (should be in P)
    print("\n1. Low treewidth instance (n=50)...")
    clauses_low, tw_low = gen.generate_low_treewidth(50)
    print(f"   Treewidth: {tw_low}, Clauses: {len(clauses_low)}")
    
    # High treewidth (should be hard)
    print("\n2. High treewidth instance (n=50)...")
    clauses_high, tw_high = gen.generate_high_treewidth(50)
    print(f"   Treewidth: {tw_high}, Clauses: {len(clauses_high)}")
    
    # Controlled treewidth
    print("\n3. Controlled treewidth instance (n=50, target_tw=10)...")
    clauses_ctrl, tw_ctrl = gen.generate_controlled_treewidth(50, 10)
    print(f"   Treewidth: {tw_ctrl}, Clauses: {len(clauses_ctrl)}")
    
    print("\n" + "="*70)
    print("✅ Instance generation complete")
    print("="*70 + "\n")


if __name__ == "__main__":
    main()
