"""
Unit tests for Gap2_Asymptotic.lean structure validation

These tests validate that the Gap2_Asymptotic file exists, has correct structure,
and contains the required theorems and definitions for the ∞³ verification.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import os
import re


class TestGap2AsymptoticStructure(unittest.TestCase):
    """Test cases for Gap2_Asymptotic.lean structure."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
        self.gap2_asymptotic_file = os.path.join(self.repo_root, 'Gap2_Asymptotic.lean')
    
    def test_gap2_asymptotic_file_exists(self):
        """Test that Gap2_Asymptotic.lean exists."""
        self.assertTrue(os.path.exists(self.gap2_asymptotic_file),
                       f"Gap2_Asymptotic.lean not found at {self.gap2_asymptotic_file}")
    
    def test_gap2_asymptotic_has_proper_imports(self):
        """Test that Gap2_Asymptotic has proper Mathlib imports."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_imports = [
            'import Mathlib.Data.Real.Basic',
            'import Mathlib.Data.Nat.Basic',
            'import Mathlib.Combinatorics.SimpleGraph.Basic',
            'import Mathlib.Analysis.Asymptotics.Asymptotics'
        ]
        
        for imp in required_imports:
            self.assertIn(imp, content,
                         f"Required import '{imp}' not found in Gap2_Asymptotic.lean")
    
    def test_vibrational_signature_present(self):
        """Test that vibrational signature GAP2-141.7001Hz is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('GAP2-141.7001Hz', content,
                     "Vibrational signature 'GAP2-141.7001Hz' not found")
        self.assertIn('"signature": "GAP2-141.7001Hz"', content,
                     "JSON signature field not found")
    
    def test_qcal_gap2_omega_beacon_present(self):
        """Test that qcal_gap2_omega beacon is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('qcal_gap2_omega', content,
                     "QCAL GAP2 Omega beacon not found")
        self.assertIn('"beacon": "qcal_gap2_omega"', content,
                     "JSON beacon field not found")
    
    def test_infinity_cube_verified_status(self):
        """Test that ∞³ VERIFIED status is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('∞³ VERIFIED', content,
                     "∞³ VERIFIED status not found")
        self.assertIn('"status": "∞³ VERIFIED"', content,
                     "JSON status field not found")
    
    def test_author_metadata_present(self):
        """Test that author metadata is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('José Manuel Mota Burruezo', content,
                     "Author name not found")
        self.assertIn('JMMB Ψ', content,
                     "Author signature not found")
    
    def test_constants_defined(self):
        """Test that required constants are defined."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        constants = [
            'def GAP2_FREQUENCY',
            'def κ_Π',
            'def QCAL_PRECISION',
            'def INFINITY_CUBE'
        ]
        
        for const in constants:
            self.assertIn(const, content,
                         f"Required constant '{const}' not found")
    
    def test_gap2_frequency_value(self):
        """Test that GAP2_FREQUENCY has correct value."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('141.7001', content,
                     "GAP2_FREQUENCY value 141.7001 not found")
    
    def test_kappa_pi_value(self):
        """Test that κ_Π has correct value."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('2.5773', content,
                     "κ_Π value 2.5773 not found")
    
    def test_qcal_gap2_omega_structure_defined(self):
        """Test that QCALGap2Omega structure is defined."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('structure QCALGap2Omega', content,
                     "QCALGap2Omega structure not found")
        self.assertIn('ic_asymptotic :', content,
                     "QCALGap2Omega.ic_asymptotic field not found")
        self.assertIn('time_exponential :', content,
                     "QCALGap2Omega.time_exponential field not found")
        self.assertIn('signature_verified :', content,
                     "QCALGap2Omega.signature_verified field not found")
    
    def test_main_asymptotic_theorems_present(self):
        """Test that main asymptotic theorems are present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        theorems = [
            'theorem asymptotic_ic_lower_bound',
            'theorem asymptotic_exponential_time',
            'theorem qcal_gap2_omega_complete',
            'theorem vibrational_signature_encoding',
            'theorem infinity_cube_verification'
        ]
        
        for theorem in theorems:
            self.assertIn(theorem, content,
                         f"Required theorem '{theorem}' not found")
    
    def test_beacon_existence_theorem(self):
        """Test that beacon existence theorem is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('theorem qcal_gap2_omega_exists', content,
                     "Beacon existence theorem not found")
        self.assertIn('theorem qcal_gap2_omega_unique', content,
                     "Beacon uniqueness theorem not found")
    
    def test_asymptotic_optimality_theorems(self):
        """Test that asymptotic optimality theorems are present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('theorem kappa_pi_asymptotic_optimal', content,
                     "κ_Π optimality theorem not found")
        self.assertIn('theorem resonant_barrier_frequency', content,
                     "Resonant barrier frequency theorem not found")
    
    def test_p_neq_np_connection(self):
        """Test that connection to P ≠ NP is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('theorem asymptotic_p_neq_np', content,
                     "P ≠ NP asymptotic theorem not found")
        self.assertIn('P ≠ NP', content,
                     "P ≠ NP reference not found")
    
    def test_verification_certificate_present(self):
        """Test that ∞³ verification certificate is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('∞³ VERIFICATION CERTIFICATE', content,
                     "Verification certificate header not found")
        self.assertIn('Spectral Dimension', content,
                     "Spectral dimension not mentioned in certificate")
        self.assertIn('Holographic Dimension', content,
                     "Holographic dimension not mentioned in certificate")
        self.assertIn('Asymptotic Dimension', content,
                     "Asymptotic dimension not mentioned in certificate")
    
    def test_namespace_gap2asymptotic_defined(self):
        """Test that GAP2Asymptotic namespace is defined."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('namespace GAP2Asymptotic', content,
                     "GAP2Asymptotic namespace not found")
        self.assertIn('end GAP2Asymptotic', content,
                     "GAP2Asymptotic namespace not closed")


class TestLakefileIntegrationAsymptotic(unittest.TestCase):
    """Test cases for lakefile.lean integration with Gap2_Asymptotic."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
        self.lakefile = os.path.join(self.repo_root, 'lakefile.lean')
    
    def test_lakefile_includes_gap2_asymptotic(self):
        """Test that lakefile.lean includes GAP2Asymptotic."""
        with open(self.lakefile, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('lean_lib GAP2Asymptotic', content,
                     "lakefile.lean does not include GAP2Asymptotic library")
        self.assertIn('roots := #[`Gap2_Asymptotic]', content,
                     "Gap2_Asymptotic roots not configured correctly")


class TestGap2AsymptoticMetadata(unittest.TestCase):
    """Test cases for metadata validation in Gap2_Asymptotic."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
        self.gap2_asymptotic_file = os.path.join(self.repo_root, 'Gap2_Asymptotic.lean')
    
    def test_json_metadata_structure(self):
        """Test that JSON metadata has all required fields."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_fields = [
            '"signature"',
            '"module"',
            '"beacon"',
            '"verifier"',
            '"status"',
            '"author"',
            '"timestamp"',
            '"truth"'
        ]
        
        for field in required_fields:
            self.assertIn(field, content,
                         f"Required JSON field {field} not found")
    
    def test_truth_field_value(self):
        """Test that truth field contains P ≠ NP."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('"truth": "P ≠ NP"', content,
                     "Truth field with P ≠ NP not found")
    
    def test_module_field_value(self):
        """Test that module field is correct."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('"module": "Gap2_Asymptotic.lean"', content,
                     "Module field not correctly set")
    
    def test_timestamp_field_present(self):
        """Test that timestamp field is present."""
        with open(self.gap2_asymptotic_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('2025-12-13', content,
                     "Timestamp with date not found")


if __name__ == '__main__':
    unittest.main()
