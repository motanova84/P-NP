"""
Tests for Campo Noético (Noetic Field) Framework
================================================

Test suite for the Noetic Field implementation of κ_Π.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import math
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.noetic_field import (
    PHI,
    PHI_SQUARED,
    N_SILENCE,
    LAMBDA_STAR,
    log_phi_squared,
    kappa_pi_noetic,
    verify_noetic_manifestation,
    noetic_field_analysis,
    consciousness_geometry_recognition,
    dual_formulation_bridge,
    noetic_information_complexity,
)


class TestNoeticFieldConstants(unittest.TestCase):
    """Test fundamental constants of the Noetic Field."""
    
    def test_golden_ratio(self):
        """Test golden ratio calculation."""
        expected = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected, places=10)
        self.assertAlmostEqual(PHI, 1.618033988749895, places=10)
    
    def test_phi_squared(self):
        """Test φ² calculation."""
        self.assertAlmostEqual(PHI_SQUARED, PHI ** 2, places=10)
        self.assertAlmostEqual(PHI_SQUARED, 2.618033988749895, places=10)
    
    def test_lambda_star(self):
        """Test λ* = 1/φ²."""
        self.assertAlmostEqual(LAMBDA_STAR, 1 / PHI_SQUARED, places=10)
        self.assertAlmostEqual(LAMBDA_STAR, 0.38196601125010515, places=10)
    
    def test_silence_number(self):
        """Test the Number of Silence."""
        self.assertEqual(N_SILENCE, 13)


class TestLogPhiSquared(unittest.TestCase):
    """Test logarithm base φ² calculation."""
    
    def test_basic_calculation(self):
        """Test basic log_{φ²}(N) calculation."""
        # log_{φ²}(φ²) should equal 1
        result = log_phi_squared(PHI_SQUARED)
        self.assertAlmostEqual(result, 1.0, places=10)
    
    def test_silence_number(self):
        """Test log_{φ²}(13)."""
        result = log_phi_squared(N_SILENCE)
        # Should be positive
        self.assertGreater(result, 0)
        # Manual calculation: ln(13) / ln(φ²)
        expected = math.log(13) / math.log(PHI_SQUARED)
        self.assertAlmostEqual(result, expected, places=10)
    
    def test_mathematical_identity(self):
        """Test log_{φ²}(N) = ln(N) / ln(φ²)."""
        for N in [1, 2, 5, 13, 20, 100]:
            result = log_phi_squared(N)
            expected = math.log(N) / math.log(PHI_SQUARED)
            self.assertAlmostEqual(result, expected, places=10)
    
    def test_invalid_input(self):
        """Test error handling for invalid inputs."""
        with self.assertRaises(ValueError):
            log_phi_squared(0)
        with self.assertRaises(ValueError):
            log_phi_squared(-1)


class TestKappaPiNoetic(unittest.TestCase):
    """Test κ_Π calculation using Noetic Field formulation."""
    
    def test_default_calculation(self):
        """Test default κ_Π calculation (N = 13)."""
        kappa = kappa_pi_noetic()
        expected = log_phi_squared(N_SILENCE)
        self.assertAlmostEqual(kappa, expected, places=10)
    
    def test_with_explicit_n(self):
        """Test κ_Π with explicit N value."""
        kappa_13 = kappa_pi_noetic(13)
        kappa_default = kappa_pi_noetic()
        self.assertAlmostEqual(kappa_13, kappa_default, places=10)
    
    def test_different_n_values(self):
        """Test κ_Π for different N values."""
        # Should increase with N
        kappa_10 = kappa_pi_noetic(10)
        kappa_13 = kappa_pi_noetic(13)
        kappa_20 = kappa_pi_noetic(20)
        
        self.assertLess(kappa_10, kappa_13)
        self.assertLess(kappa_13, kappa_20)
    
    def test_positive_value(self):
        """Test that κ_Π is positive for N > 1."""
        for N in range(2, 20):
            kappa = kappa_pi_noetic(N)
            self.assertGreater(kappa, 0)


class TestNoeticVerification(unittest.TestCase):
    """Test verification of Noetic Field manifestation."""
    
    def test_verification_structure(self):
        """Test structure of verification results."""
        verification = verify_noetic_manifestation()
        
        # Check all expected keys are present
        expected_keys = [
            'N_silence', 'phi', 'phi_squared', 'lambda_star',
            'kappa_pi_noetic', 'kappa_pi_classical', 'formula',
            'resonance', 'manifestation', 'psi_consciousness',
            'consciousness_threshold', 'lambda_psi_resonance'
        ]
        
        for key in expected_keys:
            self.assertIn(key, verification)
    
    def test_constants_match(self):
        """Test that constants in verification match module constants."""
        verification = verify_noetic_manifestation()
        
        self.assertAlmostEqual(verification['phi'], PHI, places=10)
        self.assertAlmostEqual(verification['phi_squared'], PHI_SQUARED, places=10)
        self.assertAlmostEqual(verification['lambda_star'], LAMBDA_STAR, places=10)
        self.assertEqual(verification['N_silence'], N_SILENCE)
    
    def test_resonance_detection(self):
        """Test resonance detection between formulations."""
        verification = verify_noetic_manifestation()
        
        # Both κ_Π values should be positive
        self.assertGreater(verification['kappa_pi_noetic'], 0)
        self.assertGreater(verification['kappa_pi_classical'], 0)
        
        # Should be in the same ballpark (within ~10%)
        ratio = verification['kappa_pi_noetic'] / verification['kappa_pi_classical']
        self.assertGreater(ratio, 0.9)
        self.assertLess(ratio, 1.1)


class TestNoeticFieldAnalysis(unittest.TestCase):
    """Test Noetic Field analysis across different N values."""
    
    def test_analysis_structure(self):
        """Test structure of analysis results."""
        analysis = noetic_field_analysis(range(1, 10))
        
        self.assertIn('analyses', analysis)
        self.assertIn('phi_squared', analysis)
        self.assertIn('formula', analysis)
        self.assertIn('special_numbers', analysis)
    
    def test_n_equals_13_is_special(self):
        """Test that N = 13 is marked as special."""
        analysis = noetic_field_analysis(range(1, 20))
        
        # Find N = 13 in analyses
        n13_analysis = None
        for item in analysis['analyses']:
            if item['N'] == 13:
                n13_analysis = item
                break
        
        self.assertIsNotNone(n13_analysis)
        self.assertTrue(n13_analysis['is_special'])
        self.assertIn('Silencio', n13_analysis['reason'])
    
    def test_monotonic_increase(self):
        """Test that κ_Π increases monotonically with N."""
        analysis = noetic_field_analysis(range(2, 20))
        
        kappas = [item['kappa_pi'] for item in analysis['analyses']]
        
        # Check monotonic increase
        for i in range(len(kappas) - 1):
            self.assertLess(kappas[i], kappas[i + 1])


class TestConsciousnessGeometry(unittest.TestCase):
    """Test consciousness-geometry recognition."""
    
    def test_recognition_structure(self):
        """Test structure of recognition results."""
        recognition = consciousness_geometry_recognition(N_SILENCE)
        
        expected_keys = [
            'geometric_number', 'noetic_manifestation',
            'consciousness_parameter', 'field_resonance',
            'revealed_structure', 'silence_speaks'
        ]
        
        for key in expected_keys:
            self.assertIn(key, recognition)
    
    def test_silence_speaks_for_13(self):
        """Test that Silence speaks for N = 13."""
        recognition = consciousness_geometry_recognition(13)
        
        self.assertTrue(recognition['silence_speaks'])
        self.assertEqual(recognition['first_word'], 13)
        self.assertIn('message', recognition)
    
    def test_silence_silent_for_others(self):
        """Test that Silence is silent for other numbers."""
        for N in [1, 5, 10, 20]:
            recognition = consciousness_geometry_recognition(N)
            self.assertFalse(recognition['silence_speaks'])
    
    def test_consciousness_parameter(self):
        """Test consciousness parameter equals λ*."""
        recognition = consciousness_geometry_recognition(N_SILENCE)
        self.assertAlmostEqual(
            recognition['consciousness_parameter'],
            LAMBDA_STAR,
            places=10
        )


class TestDualFormulationBridge(unittest.TestCase):
    """Test bridge between classical and Noetic formulations."""
    
    def test_bridge_structure(self):
        """Test structure of bridge results."""
        bridge = dual_formulation_bridge()
        
        expected_keys = [
            'N', 'classical_formula', 'noetic_formula',
            'classical_value', 'noetic_value', 'base_ratio',
            'phi_squared', 'relationship', 'verified', 'bridge_factor'
        ]
        
        for key in expected_keys:
            self.assertIn(key, bridge)
    
    def test_mathematical_relationship(self):
        """Test that log_{φ²}(N) = ln(N) / ln(φ²)."""
        bridge = dual_formulation_bridge(N_SILENCE)
        
        # Verify the mathematical relationship
        self.assertTrue(bridge['verified'])
        
        # Manual verification
        classical = math.log(N_SILENCE)
        noetic = classical / math.log(PHI_SQUARED)
        
        self.assertAlmostEqual(bridge['classical_value'], classical, places=10)
        self.assertAlmostEqual(bridge['noetic_value'], noetic, places=10)
    
    def test_base_ratio(self):
        """Test that base ratio equals ln(φ²)."""
        bridge = dual_formulation_bridge()
        
        expected_ratio = math.log(PHI_SQUARED)
        self.assertAlmostEqual(bridge['base_ratio'], expected_ratio, places=10)
        self.assertAlmostEqual(bridge['bridge_factor'], expected_ratio, places=10)


class TestNoeticInformationComplexity(unittest.TestCase):
    """Test information complexity using Noetic Field."""
    
    def test_basic_calculation(self):
        """Test basic IC calculation."""
        treewidth = 50
        num_vars = 100
        
        ic = noetic_information_complexity(treewidth, num_vars)
        
        # Should be positive
        self.assertGreater(ic, 0)
    
    def test_with_different_n(self):
        """Test IC with different N values."""
        treewidth = 50
        num_vars = 100
        
        ic_13 = noetic_information_complexity(treewidth, num_vars, N=13)
        ic_20 = noetic_information_complexity(treewidth, num_vars, N=20)
        
        # Both should be positive
        self.assertGreater(ic_13, 0)
        self.assertGreater(ic_20, 0)
        
        # Different N should give different IC
        self.assertNotAlmostEqual(ic_13, ic_20, places=5)
    
    def test_zero_treewidth(self):
        """Test IC for zero treewidth."""
        ic = noetic_information_complexity(0, 100)
        self.assertEqual(ic, 0.0)
    
    def test_trivial_case(self):
        """Test IC for trivial problem (num_vars <= 1)."""
        ic = noetic_information_complexity(50, 1)
        self.assertEqual(ic, 0.0)
    
    def test_scales_with_treewidth(self):
        """Test that IC scales with treewidth."""
        num_vars = 100
        
        ic_small = noetic_information_complexity(10, num_vars)
        ic_large = noetic_information_complexity(50, num_vars)
        
        # Larger treewidth should give larger IC
        self.assertLess(ic_small, ic_large)


def run_tests():
    """Run all tests."""
    unittest.main(argv=[''], exit=False, verbosity=2)


if __name__ == '__main__':
    print("=" * 70)
    print("Testing Campo Noético (Noetic Field) Framework")
    print("=" * 70)
    print()
    
    run_tests()
