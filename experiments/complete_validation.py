"""
Complete Validation Wrapper
============================

Provides a compatibility layer for the hard instance generator's benchmark_hardness method.
This wraps the existing ic_sat module functionality.

Author: José Manuel Mota Burruezo & Claude (Noēsis ∞³)
"""

import time
import multiprocessing as mp
import queue
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


def _dpll_worker(clauses, variables, queue):
    """Run DPLL in a separate process and return result through a queue."""
    try:
        queue.put(simple_dpll(clauses, variables))
    except (ValueError, TypeError, RuntimeError):
        queue.put(None)


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
                Note: this method uses the platform default multiprocessing
                context. With spawn-based defaults (Windows and macOS),
                caller code that starts processes must run under an
                `if __name__ == "__main__":` guard.
            
        Returns:
            Tuple of (time_taken, solved)
        """
        start_time = time.time()
        result_queue = mp.Queue()
        process = mp.Process(
            target=_dpll_worker,
            args=(formula.clauses, formula.variables, result_queue)
        )
        process.start()
        process.join(timeout=timeout)

        if process.is_alive():
            process.terminate()
            process.join()
            elapsed = time.time() - start_time
            return elapsed, False

        elapsed = time.time() - start_time
        try:
            result = result_queue.get(timeout=0.1)
        except queue.Empty:
            result = None
        solved = result in ['SAT', 'UNSAT']
        return elapsed, solved
