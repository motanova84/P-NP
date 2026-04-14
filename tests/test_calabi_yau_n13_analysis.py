#!/usr/bin/env python3
"""
test_calabi_yau_n13_analysis.py - Tests for N=13 Calabi-Yau resonance analysis

Tests the implementation of all 6 PASOS for the special resonance case
where N = h^{1,1} + h^{2,1} = 13.
"""

import unittest
import math
import sys
import os
import numpy as np

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_n13_analysis import (
    PHI,
    LOG_PHI2,
    KAPPA_TARGET,
    compute_kappa_phi,
    search_n13_varieties,
    ResonanceConjecture,
    predict_kappa_curve,
    find_exact_n_for_kappa,
    generate_lean4_theorem,
    run_complete_n13_analysis
)


class TestPASO1_FormalDefinition(unittest.TestCase):
    """Test PASO 1: Formal generalized definition."""
    
    def test_golden_ratio(self):
        """Test that golden ratio is correctly defined."""
        expected_phi = (1 + np.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected_phi, places=10)
        self.assertAlmostEqual(PHI, 1.618033988749895, places=10)
    
    def test_phi_squared_property(self):
        """Test golden ratio property: φ² = φ + 1."""
        phi_squared = PHI ** 2
        phi_plus_one = PHI + 1
        self.assertAlmostEqual(phi_squared, phi_plus_one, places=10)
    
    def test_log_phi2_value(self):
        """Test that ln(φ²) is correctly computed."""
        expected = np.log(PHI ** 2)
        self.assertAlmostEqual(LOG_PHI2, expected, places=10)
        # Alternative: ln(φ²) = 2·ln(φ)
        self.assertAlmostEqual(LOG_PHI2, 2 * np.log(PHI), places=10)


class TestPASO2_ObserverEncoding(unittest.TestCase):
    """Test PASO 2: Observer encoding κ_Π."""
    
    def test_compute_kappa_phi_basic(self):
        """Test basic computation of κ_Π."""
        # For any h11, h21: κ_Π = ln(h11 + h21) / ln(φ²)
        h11, h21 = 5, 8
        N = h11 + h21
        expected = np.log(N) / LOG_PHI2
        result = compute_kappa_phi(h11, h21)
        self.assertAlmostEqual(result, expected, places=10)
    
    def test_compute_kappa_phi_n13(self):
        """Test κ_Π for N=13 cases."""
        # All pairs summing to 13 should give same κ_Π
        kappa_values = []
        for h11 in range(1, 13):
            h21 = 13 - h11
            kappa = compute_kappa_phi(h11, h21)
            kappa_values.append(kappa)
        
        # All should be equal
        for kappa in kappa_values:
            self.assertAlmostEqual(kappa, kappa_values[0], places=10)
    
    def test_compute_kappa_phi_target_value(self):
        """Test that κ_Π(13) ≈ 2.6651."""
        kappa_13 = compute_kappa_phi(1, 12)
        self.assertAlmostEqual(kappa_13, KAPPA_TARGET, places=4)
    
    def test_kappa_phi_monotonicity(self):
        """Test that κ_Π is monotonically increasing with N."""
        kappa_values = []
        for N in range(1, 50):
            kappa = compute_kappa_phi(1, N-1)  # Any split works
            kappa_values.append(kappa)
        
        # Check monotonicity
        for i in range(len(kappa_values) - 1):
            self.assertLess(kappa_values[i], kappa_values[i+1])


class TestPASO3_N13Search(unittest.TestCase):
    """Test PASO 3: Search for N=13 varieties."""
    
    def test_search_n13_count(self):
        """Test that we find exactly 12 pairs for N=13."""
        df = search_n13_varieties()
        self.assertEqual(len(df), 12)
    
    def test_search_n13_all_sum_to_13(self):
        """Test that all pairs sum to 13."""
        df = search_n13_varieties()
        for _, row in df.iterrows():
            self.assertEqual(row['h11'] + row['h21'], 13)
            self.assertEqual(row['N'], 13)
    
    def test_search_n13_all_positive(self):
        """Test that all Hodge numbers are positive."""
        df = search_n13_varieties()
        for _, row in df.iterrows():
            self.assertGreater(row['h11'], 0)
            self.assertGreater(row['h21'], 0)
    
    def test_search_n13_all_same_kappa(self):
        """Test that all N=13 configurations have same κ_Π."""
        df = search_n13_varieties()
        kappa_values = df['kappa_pi'].values
        for kappa in kappa_values:
            self.assertAlmostEqual(kappa, kappa_values[0], places=10)
    
    def test_search_n13_includes_all_pairs(self):
        """Test that all expected pairs are present."""
        df = search_n13_varieties()
        expected_pairs = [(h11, 13-h11) for h11 in range(1, 13)]
        
        for expected_h11, expected_h21 in expected_pairs:
            found = False
            for _, row in df.iterrows():
                if row['h11'] == expected_h11 and row['h21'] == expected_h21:
                    found = True
                    break
            self.assertTrue(found, f"Pair ({expected_h11}, {expected_h21}) not found")
    
    def test_search_n13_ratio_calculations(self):
        """Test that h_ratio and golden ratio proximities are correct."""
        df = search_n13_varieties()
        for _, row in df.iterrows():
            expected_ratio = row['h11'] / row['h21']
            self.assertAlmostEqual(row['h_ratio'], expected_ratio, places=10)
            
            # Check proximity calculations
            self.assertAlmostEqual(row['close_to_phi'], abs(expected_ratio - PHI), places=10)
            self.assertAlmostEqual(row['close_to_phi_inv'], abs(expected_ratio - 1/PHI), places=10)


class TestPASO4_StabilityConjecture(unittest.TestCase):
    """Test PASO 4: Stability conjecture."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.conjecture = ResonanceConjecture()
    
    def test_conjecture_initialization(self):
        """Test that conjecture is properly initialized."""
        self.assertEqual(self.conjecture.N, 13)
        self.assertAlmostEqual(self.conjecture.kappa_target, KAPPA_TARGET, places=4)
    
    def test_formulate_conjecture_structure(self):
        """Test that conjecture has required components."""
        conj = self.conjecture.formulate_conjecture()
        
        # Check required keys
        required_keys = [
            'title', 'statement', 'observable_signatures',
            'mathematical_form', 'uniqueness', 'falsifiable',
            'testable_predictions'
        ]
        for key in required_keys:
            self.assertIn(key, conj)
        
        # Check types
        self.assertIsInstance(conj['title'], str)
        self.assertIsInstance(conj['observable_signatures'], list)
        self.assertIsInstance(conj['testable_predictions'], list)
        self.assertTrue(conj['falsifiable'])
    
    def test_analyze_golden_ratios(self):
        """Test golden ratio analysis for N=13 varieties."""
        df = search_n13_varieties()
        df_resonance = self.conjecture.analyze_golden_ratios(df)
        
        # Should have resonance_score column
        self.assertIn('resonance_score', df_resonance.columns)
        
        # Should be sorted by resonance_score (ascending)
        scores = df_resonance['resonance_score'].values
        self.assertTrue(all(scores[i] <= scores[i+1] for i in range(len(scores)-1)))
        
        # All scores should be non-negative
        self.assertTrue(all(score >= 0 for score in scores))


class TestPASO5_Predictions(unittest.TestCase):
    """Test PASO 5: Predictions for other N."""
    
    def test_predict_kappa_curve_shape(self):
        """Test that κ_Π curve is generated correctly."""
        N_vals, kappa_vals = predict_kappa_curve(N_min=1, N_max=50)
        
        self.assertEqual(len(N_vals), 50)
        self.assertEqual(len(kappa_vals), 50)
        
        # Should be monotonically increasing
        for i in range(len(kappa_vals) - 1):
            self.assertLess(kappa_vals[i], kappa_vals[i+1])
    
    def test_predict_kappa_curve_values(self):
        """Test specific values on the curve."""
        N_vals, kappa_vals = predict_kappa_curve(N_min=1, N_max=20)
        
        # Find N=13
        idx_13 = np.where(N_vals == 13)[0][0]
        kappa_at_13 = kappa_vals[idx_13]
        
        # Should match our target
        self.assertAlmostEqual(kappa_at_13, KAPPA_TARGET, places=4)
    
    def test_find_exact_n_for_kappa(self):
        """Test finding exact N* for target κ_Π."""
        N_exact = find_exact_n_for_kappa(KAPPA_TARGET)
        
        # Should be close to 13
        self.assertAlmostEqual(N_exact, 13, delta=0.5)
        
        # Verify: (φ²)^κ_Π = N*
        expected = (PHI**2) ** KAPPA_TARGET
        self.assertAlmostEqual(N_exact, expected, places=10)
    
    def test_find_exact_n_inverse(self):
        """Test that finding N and computing κ_Π are inverses."""
        # Start with κ_Π(13) ≈ 2.6651
        N_exact = find_exact_n_for_kappa(KAPPA_TARGET)
        
        # Compute κ_Π back from N_exact
        kappa_back = np.log(N_exact) / LOG_PHI2
        
        # Should recover original
        self.assertAlmostEqual(kappa_back, KAPPA_TARGET, places=10)
    
    def test_n13_is_closest_integer(self):
        """Test that N=13 is the closest integer to N*."""
        N_exact = find_exact_n_for_kappa(KAPPA_TARGET)
        
        # Check nearby integers
        for N in range(1, 100):
            distance_N = abs(N - N_exact)
            distance_13 = abs(13 - N_exact)
            
            if N != 13:
                # 13 should be closer or equal (within numerical precision)
                self.assertLessEqual(distance_13, distance_N + 1e-6)


class TestPASO6_Lean4Formalization(unittest.TestCase):
    """Test PASO 6: Lean4 formalization."""
    
    def test_generate_lean4_theorem_structure(self):
        """Test that Lean4 theorem is generated."""
        lean_code = generate_lean4_theorem()
        
        # Should be non-empty string
        self.assertIsInstance(lean_code, str)
        self.assertGreater(len(lean_code), 100)
    
    def test_lean4_theorem_keywords(self):
        """Test that Lean4 code contains expected keywords."""
        lean_code = generate_lean4_theorem()
        
        # Check for Lean4 keywords
        keywords = [
            'theorem', 'def', 'noncomputable',
            'Real.log', 'Real.sqrt',
            'kappa_phi_13', 'κ_Π',
            'namespace', 'CalabiYauKappaPi'
        ]
        
        for keyword in keywords:
            self.assertIn(keyword, lean_code, f"Missing keyword: {keyword}")
    
    def test_lean4_theorem_contains_target_value(self):
        """Test that theorem references the computed κ_Π(13) value."""
        lean_code = generate_lean4_theorem()
        # Should contain the computed value for κ_Π(13) ≈ 2.6651
        self.assertIn('2.6651', lean_code)
    
    def test_lean4_theorem_contains_n13(self):
        """Test that theorem references N=13."""
        lean_code = generate_lean4_theorem()
        self.assertIn('13', lean_code)


class TestCompleteAnalysis(unittest.TestCase):
    """Test the complete analysis pipeline."""
    
    def test_run_complete_analysis(self):
        """Test that complete analysis runs without errors."""
        # Redirect stdout to avoid cluttering test output
        import io
        from contextlib import redirect_stdout
        
        f = io.StringIO()
        with redirect_stdout(f):
            results = run_complete_n13_analysis()
        
        # Check results structure
        self.assertIn('n13_dataframe', results)
        self.assertIn('resonance_analysis', results)
        self.assertIn('exact_n', results)
        self.assertIn('kappa_13', results)
        self.assertIn('plot_path', results)
        self.assertIn('lean_path', results)
        self.assertIn('conjecture', results)
    
    def test_complete_analysis_values(self):
        """Test that complete analysis produces correct values."""
        import io
        from contextlib import redirect_stdout
        
        f = io.StringIO()
        with redirect_stdout(f):
            results = run_complete_n13_analysis()
        
        # Check key values
        self.assertAlmostEqual(results['kappa_13'], KAPPA_TARGET, places=4)
        self.assertAlmostEqual(results['exact_n'], 13, delta=0.5)
        
        # Check dataframe
        df = results['n13_dataframe']
        self.assertEqual(len(df), 12)
        
        # Check that files were created
        self.assertTrue(os.path.exists(results['plot_path']))
        self.assertTrue(os.path.exists(results['lean_path']))


class TestMathematicalProperties(unittest.TestCase):
    """Test mathematical properties of κ_Π."""
    
    def test_kappa_pi_equals_log_base_phi2(self):
        """Test that κ_Π(N) = log_φ²(N)."""
        for N in [5, 10, 13, 20, 30]:
            kappa = compute_kappa_phi(1, N-1)
            # log_φ²(N) = ln(N) / ln(φ²)
            expected = np.log(N) / np.log(PHI**2)
            self.assertAlmostEqual(kappa, expected, places=10)
    
    def test_inverse_relationship(self):
        """Test that N = (φ²)^κ_Π."""
        for N in [5, 10, 13, 20, 30]:
            kappa = compute_kappa_phi(1, N-1)
            N_recovered = (PHI**2) ** kappa
            self.assertAlmostEqual(N, N_recovered, places=8)
    
    def test_uniqueness_of_n13(self):
        """Test that N=13 is unique in having κ_Π(13) ≈ 2.6651."""
        tolerance = 0.001
        
        # Check integers from 1 to 100
        unique_match = None
        for N in range(1, 101):
            kappa = compute_kappa_phi(1, N-1)
            if abs(kappa - KAPPA_TARGET) < tolerance:
                self.assertIsNone(unique_match, "Multiple N values match target κ_Π")
                unique_match = N
        
        self.assertEqual(unique_match, 13)
    
    def test_kappa_bounds(self):
        """Test that κ_Π is in reasonable bounds for typical N."""
        # For N in [2, 100], κ_Π should be positive and bounded
        # (N=1 gives κ_Π=0 since ln(1)=0, so we start from N=2)
        for N in range(2, 101):
            kappa = compute_kappa_phi(1, N-1)
            self.assertGreater(kappa, 0)
            self.assertLess(kappa, 10)  # Should be well below 10


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and boundary conditions."""
    
    def test_small_n_values(self):
        """Test κ_Π for small N values."""
        # N=1
        kappa_1 = compute_kappa_phi(1, 0)  # h11=1, h21=0
        self.assertEqual(kappa_1, 0)  # ln(1) = 0
        
        # N=2
        kappa_2 = compute_kappa_phi(1, 1)
        self.assertGreater(kappa_2, 0)
    
    def test_large_n_values(self):
        """Test κ_Π for large N values."""
        # Should handle large N without issues
        kappa_1000 = compute_kappa_phi(1, 999)
        self.assertGreater(kappa_1000, KAPPA_TARGET)
        self.assertLess(kappa_1000, 15)  # Should still be reasonable
    
    def test_symmetric_pairs(self):
        """Test that (h11, h21) and (h21, h11) give same κ_Π."""
        for h11 in [1, 5, 10]:
            for h21 in [1, 5, 10]:
                kappa1 = compute_kappa_phi(h11, h21)
                kappa2 = compute_kappa_phi(h21, h11)
                self.assertAlmostEqual(kappa1, kappa2, places=10)


def run_tests():
    """Run all tests with verbose output."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
