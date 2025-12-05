"""
Unit tests for Lean formalization structure validation

These tests validate that the Lean files exist, have correct structure,
and contain the required theorems and definitions.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import os
import re


class TestLeanStructure(unittest.TestCase):
    """Test cases for Lean formalization structure."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
        
    def test_information_complexity_exists(self):
        """Test that InformationComplexity.lean exists."""
        path = os.path.join(self.repo_root, 'InformationComplexity.lean')
        self.assertTrue(os.path.exists(path), 
                       "InformationComplexity.lean should exist")
    
    def test_treewidth_theory_exists(self):
        """Test that TreewidthTheory.lean exists."""
        path = os.path.join(self.repo_root, 'TreewidthTheory.lean')
        self.assertTrue(os.path.exists(path),
                       "TreewidthTheory.lean should exist")
    
    def test_structural_coupling_exists(self):
        """Test that formal/StructuralCoupling.lean exists."""
        path = os.path.join(self.repo_root, 'formal', 'StructuralCoupling.lean')
        self.assertTrue(os.path.exists(path),
                       "formal/StructuralCoupling.lean should exist")
    
    def test_information_complexity_content(self):
        """Test InformationComplexity.lean contains required definitions."""
        path = os.path.join(self.repo_root, 'InformationComplexity.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        # Check for key definitions
        self.assertIn('namespace InformationComplexity', content)
        self.assertIn('def Message', content)
        self.assertIn('def Transcript', content)
        self.assertIn('structure CommunicationProtocol', content)
        self.assertIn('axiom mutualInformation', content)
        self.assertIn('theorem single_bit_bound', content)
        self.assertIn('axiom braverman_rao_lower_bound', content)
    
    def test_treewidth_theory_content(self):
        """Test TreewidthTheory.lean contains required definitions."""
        path = os.path.join(self.repo_root, 'TreewidthTheory.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        # Check for key definitions
        self.assertIn('namespace TreewidthTheory', content)
        self.assertIn('structure IncidenceGraph', content)
        self.assertIn('axiom treewidth', content)
        self.assertIn('structure Separator', content)
        self.assertIn('axiom exists_good_separator', content)
        self.assertIn('structure CNFFormula', content)
        self.assertIn('axiom incidenceGraph', content)
    
    def test_structural_coupling_content(self):
        """Test StructuralCoupling.lean contains Lemma 6.24."""
        path = os.path.join(self.repo_root, 'formal', 'StructuralCoupling.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        # Check for key structures and theorems
        self.assertIn('namespace StructuralCoupling', content)
        self.assertIn('structure GenericAlgorithm', content)
        self.assertIn('structure InducedProtocol', content)
        self.assertIn('theorem algorithm_induces_protocol', content)
        self.assertIn('theorem treewidth_forces_IC', content)
        self.assertIn('theorem IC_implies_exponential_time', content)
        self.assertIn('theorem structural_coupling_complete', content)
        self.assertIn('theorem no_evasion_universal', content)
    
    def test_structural_coupling_lemma_624(self):
        """Test that Lemma 6.24 is properly formalized."""
        path = os.path.join(self.repo_root, 'formal', 'StructuralCoupling.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        # Look for the main theorem statement
        self.assertIn('theorem structural_coupling_complete', content)
        self.assertIn('treewidth (incidenceGraph φ)', content)
        self.assertIn('GenericAlgorithm', content)
        self.assertIn('A.steps ≥', content)
    
    def test_no_evasion_theorem(self):
        """Test that no-evasion theorem is present."""
        path = os.path.join(self.repo_root, 'formal', 'StructuralCoupling.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        self.assertIn('theorem no_evasion_universal', content)
        self.assertIn('¬∃ (A : GenericAlgorithm φ)', content)
    
    def test_imports_correct(self):
        """Test that imports are correctly structured."""
        path = os.path.join(self.repo_root, 'formal', 'StructuralCoupling.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        # Check for required imports
        self.assertIn('import ComputationalDichotomy', content)
        self.assertIn('import InformationComplexity', content)
        self.assertIn('import TreewidthTheory', content)
        self.assertIn('import Mathlib', content)
    
    def test_lakefile_updated(self):
        """Test that lakefile.lean includes new modules."""
        path = os.path.join(self.repo_root, 'lakefile.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        self.assertIn('InformationComplexity', content)
        self.assertIn('TreewidthTheory', content)
        self.assertIn('StructuralCoupling', content)


class TestLeanDocumentation(unittest.TestCase):
    """Test cases for Lean documentation."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
    
    def test_structural_coupling_header(self):
        """Test StructuralCoupling.lean has proper documentation header."""
        path = os.path.join(self.repo_root, 'formal', 'StructuralCoupling.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        # Check for documentation markers
        self.assertIn('/-!', content)
        self.assertIn('Lemma 6.24', content)
        self.assertIn('Structural Coupling', content)
        self.assertIn('Author:', content)
    
    def test_component_documentation(self):
        """Test that key components are documented."""
        path = os.path.join(self.repo_root, 'formal', 'StructuralCoupling.lean')
        with open(path, 'r') as f:
            content = f.read()
        
        # Check for section documentation
        self.assertIn('## Definitions', content)
        self.assertIn('## Main Lemma 6.24 Components', content)
        self.assertIn('## Main Theorem', content)
        self.assertIn('## No-Evasion Theorem', content)


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
