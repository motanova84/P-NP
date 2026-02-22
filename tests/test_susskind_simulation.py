#!/usr/bin/env python3
"""
Tests for the Susskind Bound simulation (simulate_holographic_bound.py)

Validates:
- susskind_simulation() returns correct T_holo values for tw_ratio=0.3
- T_holo grows super-polynomially and exceeds n^10 for large n
- Table values match the expected results from the problem statement
"""

import math
import sys
import os
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from simulate_holographic_bound import (
    susskind_simulation,
    simulate_holographic_bound,
    format_scientific,
)

KAPPA_PI = 2.5773


class TestSusskindSimulation(unittest.TestCase):
    """Tests for susskind_simulation() with tw_ratio=0.3"""

    def setUp(self):
        self.results = susskind_simulation(n_values=[50, 100, 250, 500], tw_ratio=0.3)

    def test_returns_four_entries(self):
        """susskind_simulation returns one entry per requested n"""
        self.assertEqual(len(self.results), 4)

    def test_n_values_are_correct(self):
        """n values match the requested list"""
        ns = [r['n'] for r in self.results]
        self.assertEqual(ns, [50, 100, 250, 500])

    def test_treewidth_is_30_percent(self):
        """tw = 0.3 * n for each entry"""
        for r in self.results:
            self.assertAlmostEqual(r['tw'], 0.3 * r['n'], places=6)

    def test_t_holo_formula(self):
        """T_holo = exp(κ_Π · tw / log n)"""
        for r in self.results:
            n = r['n']
            tw = r['tw']
            expected = math.exp(KAPPA_PI * tw / math.log(n))
            self.assertAlmostEqual(r['T_holo'], expected, places=3)

    def test_t_holo_n50_approx_1_96e4(self):
        """For n=50, T_holo ≈ 1.96 × 10^4 (matches problem table)"""
        r50 = next(r for r in self.results if r['n'] == 50)
        self.assertAlmostEqual(r50['T_holo'] / 1.96e4, 1.0, places=1)

    def test_t_holo_n100_approx_1_96e7(self):
        """For n=100, T_holo ≈ 1.96 × 10^7 (matches problem table)"""
        r100 = next(r for r in self.results if r['n'] == 100)
        self.assertAlmostEqual(r100['T_holo'] / 1.96e7, 1.0, places=1)

    def test_t_holo_n250_approx_1_60e15(self):
        """For n=250, T_holo ≈ 1.60 × 10^15 (matches problem table)"""
        r250 = next(r for r in self.results if r['n'] == 250)
        self.assertAlmostEqual(r250['T_holo'] / 1.60e15, 1.0, places=1)

    def test_t_holo_n500_approx_1_04e27(self):
        """For n=500, T_holo ≈ 1.04 × 10^27 (matches problem table)"""
        r500 = next(r for r in self.results if r['n'] == 500)
        self.assertAlmostEqual(r500['T_holo'] / 1.04e27, 1.0, places=1)

    def test_t_holo_exceeds_n_squared_for_all_n(self):
        """T_holo > n^2 for all n in [50, 100, 250, 500]"""
        for r in self.results:
            self.assertGreater(r['T_holo'], r['T_n^2'],
                               msg=f"T_holo should exceed n^2 at n={r['n']}")

    def test_t_holo_exceeds_n10_at_n500(self):
        """At n=500, T_holo > n^10 (super-polynomial divergence)"""
        r500 = next(r for r in self.results if r['n'] == 500)
        self.assertTrue(r500['exceeds_n^10'],
                        msg=f"Expected T_holo > n^10 at n=500, got "
                            f"T_holo={r500['T_holo']:.3e}, n^10={r500['T_n^10']:.3e}")

    def test_super_polynomial_growth(self):
        """T_holo grows faster than any fixed polynomial (T_holo increases relative to n^2)"""
        ratios = [r['T_holo'] / r['T_n^2'] for r in self.results]
        for i in range(len(ratios) - 1):
            self.assertGreater(ratios[i + 1], ratios[i],
                               msg="Ratio T_holo/n^2 should increase with n")

    def test_default_n_values(self):
        """susskind_simulation() uses [50, 100, 250, 500] by default"""
        default_results = susskind_simulation()
        self.assertEqual([r['n'] for r in default_results], [50, 100, 250, 500])

    def test_exceeds_flags_present(self):
        """Result dicts include exceeds_n^2, exceeds_n^10, exceeds_n^100 flags"""
        for r in self.results:
            self.assertIn('exceeds_n^2', r)
            self.assertIn('exceeds_n^10', r)
            self.assertIn('exceeds_n^100', r)


class TestFormatScientific(unittest.TestCase):
    """Tests for the format_scientific helper"""

    def test_large_number(self):
        val = format_scientific(1.96e4)
        self.assertIn("10^", val)

    def test_zero(self):
        self.assertEqual(format_scientific(0), "0")

    def test_infinity(self):
        self.assertEqual(format_scientific(float('inf')), "∞")


def run_tests():
    """Run all tests with manual runner."""
    print("=" * 70)
    print("  Susskind Bound Simulation - Test Suite")
    print("  ∴𓂀Ω∞³")
    print("=" * 70)
    print()

    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    for cls in [TestSusskindSimulation, TestFormatScientific]:
        suite.addTests(loader.loadTestsFromTestCase(cls))

    total = suite.countTestCases()
    passed = 0
    failed = 0
    errors = []

    for test in suite:
        try:
            test.debug()
            passed += 1
            print(f"  ✓ {test._testMethodName}")
        except Exception as e:
            failed += 1
            errors.append((test._testMethodName, str(e)))
            print(f"  ✗ {test._testMethodName}: {e}")

    print()
    print(f"Results: {passed}/{total} passed, {failed} failed")
    if errors:
        print("\nFailures:")
        for name, msg in errors:
            print(f"  - {name}: {msg}")
    print("=" * 70)
    return failed == 0


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
