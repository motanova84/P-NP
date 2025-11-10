"""
Unit tests for Hard Instance Generator

Author: José Manuel Mota Burruezo & Claude (Noēsis ∞³)
"""

import unittest
import networkx as nx
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from experiments.hard_instance_generator import (
    CNFFormula,
    HardInstanceGenerator,
    generate_hardness_dataset
)


class TestCNFFormula(unittest.TestCase):
    """Test cases for CNFFormula dataclass."""
    
    def test_basic_formula(self):
        """Test basic CNF formula creation."""
        clauses = [[1, 2], [-1, 3], [2, -3]]
        formula = CNFFormula(variables=3, clauses=clauses)
        
        self.assertEqual(formula.variables, 3)
        self.assertEqual(len(formula.clauses), 3)
        self.assertIsNotNone(formula.incidence_graph)
    
    def test_incidence_graph_construction(self):
        """Test that incidence graph is built correctly."""
        clauses = [[1, 2], [-1, 3]]
        formula = CNFFormula(variables=3, clauses=clauses)
        
        G = formula.incidence_graph
        
        # Should have 3 variable nodes + 2 clause nodes
        self.assertEqual(len(G.nodes()), 5)
        
        # Check variable nodes exist
        self.assertTrue(G.has_node('v1'))
        self.assertTrue(G.has_node('v2'))
        self.assertTrue(G.has_node('v3'))
        
        # Check clause nodes exist
        self.assertTrue(G.has_node('c0'))
        self.assertTrue(G.has_node('c1'))
    
    def test_to_dimacs(self):
        """Test DIMACS format conversion."""
        clauses = [[1, -2], [2, 3], [-1, -3]]
        formula = CNFFormula(variables=3, clauses=clauses)
        
        dimacs = formula.to_dimacs()
        lines = dimacs.split('\n')
        
        # First line should be problem statement
        self.assertTrue(lines[0].startswith('p cnf'))
        self.assertIn('3', lines[0])  # 3 variables
        self.assertIn('3', lines[0])  # 3 clauses
        
        # Each clause line should end with 0
        for line in lines[1:]:
            self.assertTrue(line.endswith(' 0'))


class TestHardInstanceGenerator(unittest.TestCase):
    """Test cases for HardInstanceGenerator class."""
    
    def setUp(self):
        """Set up test generator."""
        self.generator = HardInstanceGenerator(seed=42)
    
    def test_generate_random_ksat(self):
        """Test random k-SAT generation."""
        n = 10
        formula = self.generator.generate_random_ksat_phase_transition(n, k=3, alpha=4.2)
        
        self.assertEqual(formula.variables, n)
        
        # Should have approximately 4.2 * n clauses
        self.assertGreater(len(formula.clauses), 30)
        self.assertLess(len(formula.clauses), 50)
        
        # Each clause should have 3 literals
        for clause in formula.clauses:
            self.assertEqual(len(clause), 3)
    
    def test_generate_tseitin_expander(self):
        """Test Tseitin formula generation over expander."""
        n = 10
        d = 3
        formula = self.generator.generate_tseitin_expander(n, d)
        
        # Should have variables for each edge in a d-regular graph
        expected_edges = (n * d) // 2
        self.assertEqual(formula.variables, expected_edges)
        
        # Should have clauses
        self.assertGreater(len(formula.clauses), 0)
    
    def test_generate_grid_sat(self):
        """Test grid SAT generation."""
        width, height = 5, 4
        formula = self.generator.generate_grid_sat(width, height)
        
        # Should have one variable per grid cell
        self.assertEqual(formula.variables, width * height)
        
        # Should have constraints
        self.assertGreater(len(formula.clauses), 0)
    
    def test_generate_treewidth_extremal(self):
        """Test high treewidth formula generation."""
        n = 20
        target_tw = 10
        formula = self.generator.generate_treewidth_extremal(n, target_tw)
        
        # Should have some variables and clauses
        self.assertGreater(formula.variables, 0)
        self.assertGreater(len(formula.clauses), 0)
    
    def test_parity_constraints(self):
        """Test parity constraint generation."""
        variables = [1, 2, 3]
        
        # Even parity (0)
        satisfying = self.generator._generate_parity_constraints(variables, 0)
        
        # Should have 4 satisfying assignments (even number of 1s)
        self.assertEqual(len(satisfying), 4)
        
        # Check that all have even parity
        for assignment in satisfying:
            self.assertEqual(sum(assignment) % 2, 0)
        
        # Odd parity (1)
        satisfying_odd = self.generator._generate_parity_constraints(variables, 1)
        
        # Should have 4 satisfying assignments (odd number of 1s)
        self.assertEqual(len(satisfying_odd), 4)
        
        # Check that all have odd parity
        for assignment in satisfying_odd:
            self.assertEqual(sum(assignment) % 2, 1)
    
    def test_find_triangles(self):
        """Test triangle finding in graphs."""
        # Create a graph with a known triangle
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2), (2, 0)])
        
        triangles = self.generator._find_triangles(G)
        
        # Should find exactly one triangle
        self.assertEqual(len(triangles), 1)
        self.assertEqual(triangles[0], (0, 1, 2))
    
    def test_graph_to_sat(self):
        """Test conversion from graph to SAT."""
        # Create a simple graph
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2), (2, 0)])  # Triangle
        
        formula = self.generator.graph_to_sat(G)
        
        # Should have 3 variables (one per edge)
        self.assertEqual(formula.variables, 3)
        
        # Should have transitivity clauses
        self.assertGreater(len(formula.clauses), 0)
    
    def test_benchmark_hardness(self):
        """Test hardness benchmarking."""
        # Create a small formula
        formula = self.generator.generate_random_ksat_phase_transition(10, k=3, alpha=4.2)
        
        # Benchmark it
        metrics = self.generator.benchmark_hardness(formula, timeout=5)
        
        # Check that all expected metrics are present
        self.assertIn('treewidth', metrics)
        self.assertIn('information_complexity', metrics)
        self.assertIn('dpll_time', metrics)
        self.assertIn('dpll_solved', metrics)
        self.assertIn('n_vars', metrics)
        self.assertIn('n_clauses', metrics)
        self.assertIn('clause_variable_ratio', metrics)
        self.assertIn('graph_density', metrics)
        
        # Check that metrics have reasonable values
        self.assertEqual(metrics['n_vars'], 10)
        self.assertGreater(metrics['n_clauses'], 0)
        self.assertGreater(metrics['clause_variable_ratio'], 0)


class TestDatasetGeneration(unittest.TestCase):
    """Test cases for dataset generation."""
    
    def test_generate_small_dataset(self):
        """Test generation of a small dataset."""
        import tempfile
        import shutil
        import os
        
        # Create temporary directory
        temp_dir = tempfile.mkdtemp()
        
        try:
            # Generate small dataset
            sizes = [10, 20]
            dataset = generate_hardness_dataset(sizes, output_dir=temp_dir)
            
            # Check that dataset has entries for each size
            self.assertIn(10, dataset)
            self.assertIn(20, dataset)
            
            # Check that each size has all instance types
            for size in sizes:
                self.assertIn('tseitin_expander', dataset[size])
                self.assertIn('random_3sat', dataset[size])
                self.assertIn('high_treewidth', dataset[size])
                self.assertIn('grid_sat', dataset[size])
            
            # Check that files were created
            self.assertTrue(os.path.exists(f"{temp_dir}/n10_tseitin_expander.cnf"))
            self.assertTrue(os.path.exists(f"{temp_dir}/n10_random_3sat.cnf"))
            self.assertTrue(os.path.exists(f"{temp_dir}/hardness_benchmarks.json"))
        
        finally:
            # Clean up
            shutil.rmtree(temp_dir)


if __name__ == '__main__':
    print("Running Hard Instance Generator Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
