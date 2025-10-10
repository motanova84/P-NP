"""
Integration tests for the complete P-NP framework

Tests the interaction between:
- Computational dichotomy module
- Tseitin generator
- IC-SAT solver
- CNF file utilities

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os
import tempfile

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.computational_dichotomy import CNFFormula, generate_low_treewidth_formula
from src.gadgets.tseitin_generator import TseitinGenerator, generate_expander_tseitin
from src.ic_sat import (
    ic_sat, simple_dpll, compare_treewidths,
    LargeScaleValidation, build_incidence_graph
)
from src.cnf_utils import read_cnf_file, write_cnf_file, cnf_to_string


class TestIntegration(unittest.TestCase):
    """Integration tests for the complete framework."""
    
    def test_low_treewidth_pipeline(self):
        """Test complete pipeline for low treewidth formula."""
        # Generate low treewidth formula
        formula = generate_low_treewidth_formula(10)
        
        # Check treewidth
        primal_tw, incidence_tw = compare_treewidths(
            formula.num_vars, 
            formula.clauses
        )
        
        # Should be low
        self.assertLessEqual(primal_tw, 3)
        self.assertLessEqual(incidence_tw, 3)
        
        # Solve with IC-SAT
        result = ic_sat(formula.num_vars, formula.clauses, log=False)
        
        # Should be solvable (though may be UNSAT)
        self.assertIn(result, ['SAT', 'UNSAT'])
    
    def test_tseitin_to_ic_sat(self):
        """Test Tseitin formula generation and solving with IC-SAT."""
        import networkx as nx
        
        # Create a small graph
        G = nx.cycle_graph(4)
        
        # Generate Tseitin formula
        generator = TseitinGenerator(G)
        
        # Even charges (satisfiable)
        num_vars, clauses = generator.generate_formula([0, 0, 0, 0])
        
        self.assertGreater(num_vars, 0)
        self.assertGreater(len(clauses), 0)
        
        # Solve with IC-SAT
        result = ic_sat(num_vars, clauses, log=False)
        
        self.assertEqual(result, 'SAT')
    
    def test_cnf_file_roundtrip(self):
        """Test writing and reading CNF files."""
        # Create a formula
        num_vars = 3
        clauses = [[1, 2], [-1, 3], [-2, -3]]
        
        # Write to temp file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False) as f:
            temp_file = f.name
        
        try:
            write_cnf_file(temp_file, num_vars, clauses, 
                          comments=["Test formula"])
            
            # Read back
            num_vars_read, clauses_read = read_cnf_file(temp_file)
            
            # Should match
            self.assertEqual(num_vars, num_vars_read)
            self.assertEqual(clauses, clauses_read)
        finally:
            if os.path.exists(temp_file):
                os.unlink(temp_file)
    
    def test_cnf_formula_incidence_graph(self):
        """Test CNFFormula's incidence graph matches ic_sat's."""
        num_vars = 3
        clauses = [[1, 2], [2, 3]]
        
        # Create CNFFormula
        formula = CNFFormula(num_vars, clauses)
        
        # Build with ic_sat
        G_ic = build_incidence_graph(num_vars, clauses)
        
        # Both should have same structure
        self.assertEqual(len(formula.incidence_graph.nodes()), 
                        len(G_ic.nodes()))
        self.assertEqual(len(formula.incidence_graph.edges()), 
                        len(G_ic.edges()))
        
        # Check bipartite labels exist
        for node, data in G_ic.nodes(data=True):
            self.assertIn('bipartite', data)
    
    def test_validation_framework_complete(self):
        """Test complete validation framework."""
        validator = LargeScaleValidation()
        
        # Generate instance
        n_vars, clauses = validator.generate_3sat_critical(10)
        
        # Estimate treewidth
        primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
        
        self.assertGreater(primal_tw, 0)
        self.assertGreater(incidence_tw, 0)
        
        # Run IC-SAT
        result = validator.run_ic_sat(n_vars, clauses)
        
        self.assertIn(result, ['SAT', 'UNSAT', 'TIMEOUT'])
    
    def test_dpll_vs_ic_sat_consistency(self):
        """Test that DPLL and IC-SAT agree on small formulas."""
        test_cases = [
            # (n_vars, clauses, expected)
            (2, [[1, 2], [-1, -2]], 'SAT'),
            (1, [[1], [-1]], 'UNSAT'),
            (3, [[1], [-1, 2], [-2, 3]], 'SAT'),
        ]
        
        for n_vars, clauses, expected in test_cases:
            dpll_result = simple_dpll(clauses, n_vars)
            ic_result = ic_sat(n_vars, clauses, log=False)
            
            # Both should agree
            self.assertEqual(dpll_result, ic_result)
            # And match expected
            self.assertEqual(dpll_result, expected)
    
    def test_expander_tseitin_high_treewidth(self):
        """Test that expander Tseitin formulas have high treewidth."""
        num_vars, clauses = generate_expander_tseitin(20, 3)
        
        primal_tw, incidence_tw = compare_treewidths(num_vars, clauses)
        
        # Should have higher treewidth than chain
        chain_formula = generate_low_treewidth_formula(20)
        chain_tw, _ = compare_treewidths(
            chain_formula.num_vars,
            chain_formula.clauses
        )
        
        # Expander should have higher treewidth
        self.assertGreater(primal_tw, chain_tw)
    
    def test_cnf_to_string_format(self):
        """Test CNF to string conversion."""
        num_vars = 2
        clauses = [[1, -2], [-1, 2]]
        
        string = cnf_to_string(num_vars, clauses)
        
        # Should contain key information
        self.assertIn('2 variables', string)
        self.assertIn('2 clauses', string)
        self.assertIn('x1', string)
        self.assertIn('¬x2', string)
    
    def test_example_cnf_file(self):
        """Test reading the example CNF file."""
        example_file = os.path.join(
            os.path.dirname(__file__), 
            '..', 
            'examples', 
            'sat', 
            'simple_example.cnf'
        )
        
        if os.path.exists(example_file):
            num_vars, clauses = read_cnf_file(example_file)
            
            # Should have variables and clauses
            self.assertGreater(num_vars, 0)
            self.assertGreater(len(clauses), 0)
            
            # Should be solvable
            result = ic_sat(num_vars, clauses, log=False)
            self.assertIn(result, ['SAT', 'UNSAT'])


class TestComputationalDichotomy(unittest.TestCase):
    """Test the computational dichotomy framework."""
    
    def test_dichotomy_treewidth_correlation(self):
        """Test that treewidth correlates with solving difficulty."""
        # Low treewidth (should be easier)
        low_formula = generate_low_treewidth_formula(20)
        low_tw, _ = compare_treewidths(
            low_formula.num_vars,
            low_formula.clauses
        )
        
        # High treewidth (should be harder)
        high_vars, high_clauses = generate_expander_tseitin(20, 3)
        high_tw, _ = compare_treewidths(high_vars, high_clauses)
        
        # High should have higher treewidth
        self.assertGreater(high_tw, low_tw)
    
    def test_cnf_formula_class(self):
        """Test CNFFormula class functionality."""
        formula = generate_low_treewidth_formula(10)
        
        # Should have proper attributes
        self.assertEqual(formula.num_vars, 10)
        self.assertGreater(len(formula.clauses), 0)
        self.assertIsNotNone(formula.incidence_graph)
        
        # Should compute treewidth
        tw = formula.compute_treewidth_approximation()
        self.assertGreaterEqual(tw, 0)
        
        # Should have string representation
        str_repr = str(formula)
        self.assertIn('CNFFormula', str_repr)
        self.assertIn('10', str_repr)


if __name__ == '__main__':
    print("Running Integration Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
