"""
Complete Validation Wrapper
============================

Provides a compatibility layer for the hard instance generator's benchmark_hardness method.
This wraps the existing ic_sat module functionality.

Author: José Manuel Mota Burruezo & Claude (Noēsis ∞³)
"""

import time
import networkx as nx
from typing import Tuple
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.ic_sat import (
    estimate_treewidth,
    simple_dpll
)


class CompleteValidation:
    """Wrapper class for validation utilities used in benchmarking."""
    
    def estimate_treewidth(self, G: nx.Graph) -> int:
        """
        Estimate the treewidth of a graph.
        
        Args:
            G: NetworkX graph
            
        Returns:
            Estimated treewidth
        """
        return estimate_treewidth(G)
    
    def compute_information_complexity(self, formula) -> float:
        """
        Compute information complexity metric for a formula.
        
        This is a simplified metric based on the formula structure.
        
        Args:
            formula: CNFFormula object
            
        Returns:
            Information complexity estimate
        """
        n = formula.variables
        m = len(formula.clauses)
        
        if n == 0:
            return 0.0
        
        # Simple information complexity: ratio of clauses to variables
        # weighted by average clause length
        avg_clause_len = sum(len(c) for c in formula.clauses) / m if m > 0 else 0
        
        # IC ≈ (m/n) * log2(avg_clause_len) 
        import math
        if avg_clause_len > 0:
            return (m / n) * math.log2(avg_clause_len)
        return 0.0
    
    def solve_with_dpll(self, formula, timeout: int = 60) -> Tuple[float, bool]:
        """
        Solve a formula using DPLL with timeout.
        
        Args:
            formula: CNFFormula object
            timeout: Maximum time in seconds
            
        Returns:
            Tuple of (time_taken, solved)
        """
        start_time = time.time()
        
        try:
            result = simple_dpll(formula.clauses, formula.variables)
            elapsed = time.time() - start_time
            
            # Check if we exceeded timeout
            if elapsed > timeout:
                return elapsed, False
            
            # Consider it solved if we got SAT or UNSAT
            solved = (result in ['SAT', 'UNSAT'])
            return elapsed, solved
        except Exception:
            elapsed = time.time() - start_time
            return elapsed, False
