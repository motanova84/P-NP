#!/usr/bin/env python3
"""
Tests for Fermion-Higgs Lagrangian P=NP Framework
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³

Tests for:
- FermionHiggsLagrangian (ℒ_int = -g_eff ψ ψ̄ H)
- CabelloUnit (simultaneous configuration exploration)
- BerryPhaseOracle (γ_B = 2πn validation)
- Integrated P=NP framework
"""

import unittest
import sys
import os
import numpy as np

# Add repository root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from src.fermion_higgs_lagrangian import (
    FermionHiggsLagrangian,
    FermionHiggsNPOracle,
    HiggsParameters,
    FermionState,
    QuantumCoherenceField,
    get_pc_higgs_parameters,
    calculate_mass_reduction,
    F0_HZ,
    T0_MS,
    PC_HIGGS_MASS_GEV,
    HIGGS_MASS_STANDARD_GEV,
    MASS_REDUCTION_FACTOR
)

from src.cabello_unit import (
    CabelloUnit,
    ParallelConfigurationExplorer,
    ConfigurationState,
    CabelloContext
)

from src.berry_phase_oracle import (
    BerryPhaseOracle,
    BerryPhaseCalculator,
    BerryState,
    ParameterPath,
    IntegratedBerryHiggsOracle,
    TWO_PI,
    PHASE_TOLERANCE
)


class TestPhysicalConstants(unittest.TestCase):
    """Test physical constants are correctly defined."""
    
    def test_higgs_mass_standard(self):
        """Verify standard Higgs mass."""
        self.assertAlmostEqual(HIGGS_MASS_STANDARD_GEV, 125.1, places=1)
    
    def test_higgs_mass_pc(self):
        """Verify PC-Higgs mass reduction."""
        expected = HIGGS_MASS_STANDARD_GEV * (1 - MASS_REDUCTION_FACTOR)
        self.assertAlmostEqual(PC_HIGGS_MASS_GEV, expected, places=3)
        # Approximately 118.375 GeV
        self.assertTrue(118.0 < PC_HIGGS_MASS_GEV < 119.0)
    
    def test_mass_reduction_factor(self):
        """Verify 5.38% mass reduction."""
        self.assertAlmostEqual(MASS_REDUCTION_FACTOR, 0.0538, places=4)
    
    def test_fundamental_frequency(self):
        """Verify fundamental frequency f₀ = 141.7001 Hz."""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
    
    def test_fundamental_period(self):
        """Verify fundamental period T₀ ≈ 7.0572 ms."""
        expected_t0 = 1000.0 / F0_HZ
        self.assertAlmostEqual(T0_MS, expected_t0, places=4)
        self.assertTrue(7.05 < T0_MS < 7.06)


class TestHiggsParameters(unittest.TestCase):
    """Test HiggsParameters dataclass."""
    
    def test_default_initialization(self):
        """Test default parameter values."""
        params = HiggsParameters()
        self.assertEqual(params.mass_standard_gev, HIGGS_MASS_STANDARD_GEV)
        self.assertEqual(params.mass_pc_gev, PC_HIGGS_MASS_GEV)
        self.assertEqual(params.reduction_factor, MASS_REDUCTION_FACTOR)
    
    def test_custom_initialization(self):
        """Test custom parameter values."""
        params = HiggsParameters(
            mass_standard_gev=126.0,
            mass_pc_gev=120.0,
            reduction_factor=0.05,
            g_eff=0.95
        )
        self.assertEqual(params.mass_standard_gev, 126.0)
        self.assertEqual(params.g_eff, 0.95)


class TestFermionState(unittest.TestCase):
    """Test FermionState dataclass."""
    
    def test_state_creation(self):
        """Test fermion state creation."""
        state = FermionState(
            amplitude=complex(0.7, 0.3),
            spin=0.5,
            mass_gev=0.511
        )
        self.assertEqual(state.spin, 0.5)
        self.assertFalse(state.is_antiparticle)
    
    def test_psi_bar(self):
        """Test adjoint state ψ̄."""
        state = FermionState(
            amplitude=complex(0.7, 0.3),
            spin=0.5,
            mass_gev=0.511
        )
        psi_bar = state.psi_bar
        
        # Check conjugate amplitude
        self.assertEqual(psi_bar.amplitude, np.conj(state.amplitude))
        # Check spin flip
        self.assertEqual(psi_bar.spin, -state.spin)
        # Check antiparticle flag
        self.assertTrue(psi_bar.is_antiparticle)


class TestFermionHiggsLagrangian(unittest.TestCase):
    """Test FermionHiggsLagrangian class."""
    
    def setUp(self):
        """Initialize Lagrangian for tests."""
        self.lagrangian = FermionHiggsLagrangian()
    
    def test_initialization(self):
        """Test Lagrangian initialization."""
        self.assertIsNotNone(self.lagrangian.higgs)
        self.assertEqual(self.lagrangian.higgs.mass_standard_gev, HIGGS_MASS_STANDARD_GEV)
    
    def test_effective_coupling(self):
        """Test effective coupling calculation."""
        # At full coherence
        g_eff_1 = self.lagrangian.effective_coupling(1.0)
        self.assertGreater(g_eff_1, 0)
        
        # At zero coherence
        g_eff_0 = self.lagrangian.effective_coupling(0.0)
        self.assertEqual(g_eff_0, 0.0)
        
        # Proportional relationship
        g_eff_half = self.lagrangian.effective_coupling(0.5)
        self.assertAlmostEqual(g_eff_half, g_eff_1 * 0.5, places=6)
    
    def test_effective_higgs_mass(self):
        """Test effective Higgs mass under coherence."""
        # At zero coherence: standard mass
        mass_0 = self.lagrangian.effective_higgs_mass(0.0)
        self.assertAlmostEqual(mass_0, HIGGS_MASS_STANDARD_GEV, places=6)
        
        # At full coherence: PC-Higgs mass
        mass_1 = self.lagrangian.effective_higgs_mass(1.0)
        self.assertAlmostEqual(mass_1, PC_HIGGS_MASS_GEV, places=3)
        
        # Reduction is ~5.38%
        reduction = (mass_0 - mass_1) / mass_0
        self.assertAlmostEqual(reduction, MASS_REDUCTION_FACTOR, places=4)
    
    def test_spacetime_viscosity(self):
        """Test spacetime viscosity calculation."""
        # At zero coherence: viscosity = 1.0
        visc_0 = self.lagrangian.spacetime_viscosity(0.0)
        self.assertAlmostEqual(visc_0, 1.0, places=6)
        
        # At full coherence: reduced viscosity
        visc_1 = self.lagrangian.spacetime_viscosity(1.0)
        self.assertLess(visc_1, 1.0)
        self.assertAlmostEqual(visc_1, 1 - MASS_REDUCTION_FACTOR, places=4)
    
    def test_collapse_time(self):
        """Test solution collapse time."""
        # At full coherence: T₀
        time_1 = self.lagrangian.collapse_time(1.0)
        self.assertAlmostEqual(time_1, T0_MS, places=4)
        
        # At half coherence: 2*T₀
        time_half = self.lagrangian.collapse_time(0.5)
        self.assertAlmostEqual(time_half, 2 * T0_MS, places=4)
        
        # At zero coherence: infinite
        time_0 = self.lagrangian.collapse_time(0.0)
        self.assertEqual(time_0, float('inf'))
    
    def test_flash_time_achievable(self):
        """Test flash time achievement check."""
        # At full coherence: achievable
        self.assertTrue(self.lagrangian.is_flash_time_achievable(1.0))
        
        # At low coherence: not achievable
        self.assertFalse(self.lagrangian.is_flash_time_achievable(0.3))
    
    def test_lagrangian_density(self):
        """Test Lagrangian density calculation."""
        psi = FermionState(amplitude=complex(1.0, 0), spin=0.5, mass_gev=0.511)
        H = 246.22  # VEV
        
        L = self.lagrangian.lagrangian_density(psi, H, coherence=1.0)
        
        # Should be negative (attractive interaction)
        self.assertLess(L, 0)


class TestQuantumCoherenceField(unittest.TestCase):
    """Test QuantumCoherenceField class."""
    
    def test_initialization(self):
        """Test field initialization."""
        field = QuantumCoherenceField(10)
        self.assertEqual(field.n_configurations, 10)
        self.assertEqual(len(field.amplitudes), 10)
    
    def test_uniform_superposition(self):
        """Test uniform amplitude initialization."""
        n = 4
        field = QuantumCoherenceField(n)
        
        # Each amplitude should be 1/√n
        expected_amp = 1.0 / np.sqrt(n)
        for amp in field.amplitudes:
            self.assertAlmostEqual(np.abs(amp), expected_amp, places=6)
    
    def test_coherence_level(self):
        """Test coherence level calculation."""
        field = QuantumCoherenceField(4)
        
        # Initial coherence should be close to 1
        coherence = field.coherence_level()
        self.assertGreaterEqual(coherence, 0)
        self.assertLessEqual(coherence, 1)
    
    def test_collapse_to_solution(self):
        """Test solution collapse."""
        field = QuantumCoherenceField(5)
        
        # Artificially boost one amplitude
        field.amplitudes[2] = complex(0.9, 0)
        
        idx, prob = field.collapse_to_solution()
        
        # Should select index 2
        self.assertEqual(idx, 2)
        self.assertGreater(prob, 0)


class TestFermionHiggsNPOracle(unittest.TestCase):
    """Test FermionHiggsNPOracle class."""
    
    def setUp(self):
        """Initialize oracle for tests."""
        self.oracle = FermionHiggsNPOracle()
        self.search_space = [
            "config_001",
            "config_002",
            "config_003",
            "config_004"
        ]
    
    def test_encode_configuration(self):
        """Test configuration encoding."""
        state = self.oracle.encode_configuration("test_config")
        
        self.assertIsInstance(state, FermionState)
        self.assertIsInstance(state.amplitude, complex)
        self.assertIn(state.spin, [0.5, -0.5])
    
    def test_evaluate_resonance(self):
        """Test resonance evaluation."""
        result = self.oracle.evaluate_resonance(self.search_space)
        
        # Check required fields
        self.assertIn('solution', result)
        self.assertIn('coherence', result)
        self.assertIn('collapse_time_ms', result)
        self.assertIn('higgs_mass_gev', result)
        self.assertIn('viscosity', result)
        
        # Solution should be in search space
        self.assertIn(result['solution'], self.search_space)
    
    def test_solve_np(self):
        """Test NP solving."""
        result = self.oracle.solve_np(self.search_space)
        
        # Check required fields
        self.assertIn('solution', result)
        self.assertIn('complexity', result)
        self.assertIn('lagrangian', result)
        self.assertIn('pc_higgs_mass_gev', result)
        
        # Lagrangian should be the interaction form
        self.assertEqual(result['lagrangian'], 'ℒ_int = -g_eff ψ ψ̄ H')
    
    def test_empty_search_space(self):
        """Test handling of empty search space."""
        result = self.oracle.evaluate_resonance([])
        
        self.assertIsNone(result['solution'])
        self.assertEqual(result['coherence'], 0.0)


class TestCabelloUnit(unittest.TestCase):
    """Test CabelloUnit class."""
    
    def setUp(self):
        """Initialize Cabello unit for tests."""
        self.configs = ["config_a", "config_b", "config_c", "config_d"]
        self.unit = CabelloUnit(self.configs)
    
    def test_initialization(self):
        """Test unit initialization."""
        self.assertEqual(self.unit.n_configs, 4)
        self.assertEqual(self.unit.configurations, self.configs)
        self.assertFalse(self.unit._initialized)
    
    def test_prepare_superposition(self):
        """Test superposition preparation."""
        self.unit.prepare_superposition()
        
        self.assertTrue(self.unit._initialized)
        self.assertEqual(len(self.unit.states), 4)
        
        # All amplitudes should be equal
        amp = self.unit.states[0].amplitude
        for state in self.unit.states[1:]:
            self.assertAlmostEqual(np.abs(state.amplitude), np.abs(amp), places=6)
    
    def test_explore_all(self):
        """Test parallel exploration."""
        self.unit.prepare_superposition()
        self.unit.explore_all()
        
        self.assertTrue(self.unit._explored)
        
        # All states should be evaluated
        for state in self.unit.states:
            self.assertTrue(state.evaluated)
    
    def test_extract_solution(self):
        """Test solution extraction."""
        self.unit.prepare_superposition()
        self.unit.explore_all()
        
        solution, metadata = self.unit.extract_solution()
        
        # Solution should be in configurations
        self.assertIn(solution, self.configs)
        
        # Metadata should have required fields
        self.assertIn('probability', metadata)
        self.assertIn('coherence', metadata)
        self.assertIn('complexity', metadata)
    
    def test_coherence_level(self):
        """Test coherence calculation."""
        self.unit.prepare_superposition()
        
        coherence = self.unit.coherence_level()
        
        self.assertGreaterEqual(coherence, 0)
        self.assertLessEqual(coherence, 1)
    
    def test_probability_distribution(self):
        """Test probability distribution."""
        self.unit.prepare_superposition()
        
        probs = self.unit.get_probability_distribution()
        
        self.assertEqual(len(probs), 4)
        # All probabilities should sum to ~1
        self.assertAlmostEqual(np.sum(probs), 1.0, places=5)
    
    def test_empty_configuration_error(self):
        """Test error on empty configuration."""
        with self.assertRaises(ValueError):
            CabelloUnit([])


class TestParallelConfigurationExplorer(unittest.TestCase):
    """Test ParallelConfigurationExplorer class."""
    
    def setUp(self):
        """Initialize explorer for tests."""
        self.configs = ["opt_1", "opt_2", "optimal_solution", "opt_3"]
        self.explorer = ParallelConfigurationExplorer(self.configs)
    
    def test_find_optimum(self):
        """Test optimum finding."""
        def fitness(config):
            if "optimal" in config:
                return 0.95
            return 0.3
        
        solution, metadata = self.explorer.find_optimum(fitness)
        
        # Should find the optimal one
        self.assertEqual(solution, "optimal_solution")
        self.assertIn('probability', metadata)
    
    def test_find_satisfying(self):
        """Test constraint satisfaction."""
        def constraint(config):
            return "optimal" in config
        
        solution, metadata = self.explorer.find_satisfying(constraint)
        
        self.assertEqual(solution, "optimal_solution")
        self.assertTrue(metadata['satisfies_constraint'])
    
    def test_explore_metrics(self):
        """Test exploration metrics."""
        metrics = self.explorer.explore_metrics()
        
        self.assertIn('n_configurations', metrics)
        self.assertIn('coherence', metrics)
        self.assertIn('entropy', metrics)


class TestBerryState(unittest.TestCase):
    """Test BerryState dataclass."""
    
    def test_state_creation(self):
        """Test state creation."""
        state = BerryState(
            configuration="test",
            amplitude=complex(1, 0),
            accumulated_phase=0.0
        )
        self.assertEqual(state.configuration, "test")
        self.assertFalse(state.is_quantized)
    
    def test_total_phase(self):
        """Test total phase calculation."""
        state = BerryState(
            configuration="test",
            amplitude=complex(1, 0),
            accumulated_phase=np.pi,
            cycle_count=2
        )
        expected = np.pi + 2 * TWO_PI
        self.assertAlmostEqual(state.total_phase, expected, places=6)
    
    def test_check_quantization(self):
        """Test phase quantization check."""
        # Quantized phase (2π)
        state1 = BerryState("test1", complex(1, 0), TWO_PI)
        self.assertTrue(state1.check_quantization())
        self.assertEqual(state1.winding_number, 1)
        
        # Non-quantized phase
        state2 = BerryState("test2", complex(1, 0), np.pi)
        self.assertFalse(state2.check_quantization())


class TestParameterPath(unittest.TestCase):
    """Test ParameterPath dataclass."""
    
    def test_path_creation(self):
        """Test path creation."""
        center = np.array([0.5, 0.5, 0.5])
        path = ParameterPath(
            dimension=3,
            n_points=10,
            center=center,
            radius=0.3
        )
        
        self.assertEqual(path.n_points, 10)
        self.assertEqual(len(path.points), 10)
    
    def test_path_is_cyclic(self):
        """Test that path is approximately cyclic."""
        center = np.array([0, 0, 0])
        path = ParameterPath(
            dimension=3,
            n_points=100,
            center=center,
            radius=1.0
        )
        
        # First and last points should be close (cyclic)
        first = path.points[0]
        last = path.points[-1]
        
        # In first two dimensions, should form a circle
        dist_first = np.sqrt(first[0]**2 + first[1]**2)
        dist_last = np.sqrt(last[0]**2 + last[1]**2)
        
        self.assertAlmostEqual(dist_first, 1.0, places=4)
        self.assertAlmostEqual(dist_last, 1.0, places=4)


class TestBerryPhaseCalculator(unittest.TestCase):
    """Test BerryPhaseCalculator class."""
    
    def setUp(self):
        """Initialize calculator for tests."""
        self.calculator = BerryPhaseCalculator(dimension=3, n_path_points=50)
    
    def test_configuration_to_state(self):
        """Test configuration to state mapping."""
        state = self.calculator.configuration_to_state(
            "test_config",
            np.array([0.5, 0.5, 0.5])
        )
        
        # State should be normalized
        norm = np.linalg.norm(state)
        self.assertAlmostEqual(norm, 1.0, places=5)
    
    def test_calculate_connection(self):
        """Test connection calculation."""
        state1 = np.array([1, 0, 0, 0], dtype=complex)
        state2 = np.array([1, 0, 0, 0], dtype=complex)
        
        overlap = self.calculator.calculate_connection(state1, state2)
        
        self.assertAlmostEqual(np.abs(overlap), 1.0, places=6)
    
    def test_calculate_phase(self):
        """Test phase calculation."""
        center = np.array([0.5, 0.5, 0.5])
        path = ParameterPath(3, 50, center, 0.5)
        
        berry_state = self.calculator.calculate_phase("test_config", path)
        
        # Phase should be real number
        self.assertIsInstance(berry_state.accumulated_phase, float)


class TestBerryPhaseOracle(unittest.TestCase):
    """Test BerryPhaseOracle class."""
    
    def setUp(self):
        """Initialize oracle for tests."""
        self.oracle = BerryPhaseOracle(dimension=3, n_path_points=50)
        self.configs = ["config_a", "config_b", "config_c"]
    
    def test_evaluate(self):
        """Test configuration evaluation."""
        state = self.oracle.evaluate("test_config")
        
        self.assertIsInstance(state, BerryState)
        self.assertIsInstance(state.accumulated_phase, float)
    
    def test_is_solution(self):
        """Test solution check."""
        # This depends on hash, so just check it returns bool
        result = self.oracle.is_solution("test_config")
        self.assertIsInstance(result, bool)
    
    def test_find_solutions(self):
        """Test finding solutions."""
        solutions, states = self.oracle.find_solutions(self.configs)
        
        self.assertIsInstance(solutions, list)
        self.assertIsInstance(states, dict)
        
        # All configs should have states
        for config in self.configs:
            self.assertIn(config, states)
    
    def test_rank_by_quantization(self):
        """Test ranking by quantization."""
        ranked = self.oracle.rank_by_quantization(self.configs)
        
        self.assertEqual(len(ranked), len(self.configs))
        
        # Should be sorted by deviation
        deviations = [r[1] for r in ranked]
        self.assertEqual(deviations, sorted(deviations))
    
    def test_solve_np(self):
        """Test NP solving."""
        result = self.oracle.solve_np(self.configs)
        
        # Check required fields
        self.assertIn('solution', result)
        self.assertIn('berry_phase', result)
        self.assertIn('complexity', result)
        
        # Complexity should be O(1)
        self.assertEqual(result['complexity'], 'O(1)')
    
    def test_empty_search_space(self):
        """Test empty search space."""
        result = self.oracle.solve_np([])
        
        self.assertIsNone(result['solution'])


class TestIntegratedBerryHiggsOracle(unittest.TestCase):
    """Test IntegratedBerryHiggsOracle class."""
    
    def setUp(self):
        """Initialize integrated oracle for tests."""
        self.oracle = IntegratedBerryHiggsOracle()
        self.configs = ["test_1", "test_2", "test_3"]
    
    def test_solve(self):
        """Test integrated solving."""
        result = self.oracle.solve(self.configs, coherence=1.0)
        
        # Check combined fields from both frameworks
        self.assertIn('solution', result)
        self.assertIn('berry_phase', result)
        self.assertIn('effective_higgs_mass_gev', result)
        self.assertIn('framework', result)
        
        # Check framework identification
        self.assertEqual(result['framework'], 'Fermion-Higgs + Berry Phase')
    
    def test_solve_with_coherence(self):
        """Test solving with different coherence levels."""
        result_full = self.oracle.solve(self.configs, coherence=1.0)
        result_half = self.oracle.solve(self.configs, coherence=0.5)
        
        # Higher coherence should give lower effective mass
        self.assertLess(
            result_full['effective_higgs_mass_gev'],
            result_half['effective_higgs_mass_gev']
        )
        
        # Higher coherence should give shorter collapse time
        self.assertLess(
            result_full['collapse_time_ms'],
            result_half['collapse_time_ms']
        )


class TestUtilityFunctions(unittest.TestCase):
    """Test utility functions."""
    
    def test_get_pc_higgs_parameters(self):
        """Test getting PC-Higgs parameters."""
        params = get_pc_higgs_parameters()
        
        self.assertIn('standard_higgs_mass_gev', params)
        self.assertIn('pc_higgs_mass_gev', params)
        self.assertIn('mass_reduction_percent', params)
        self.assertIn('fundamental_period_ms', params)
        
        # Check values
        self.assertAlmostEqual(
            params['mass_reduction_percent'],
            MASS_REDUCTION_FACTOR * 100,
            places=2
        )
    
    def test_calculate_mass_reduction(self):
        """Test mass reduction calculation."""
        # At full coherence
        reduction_1 = calculate_mass_reduction(1.0)
        self.assertAlmostEqual(reduction_1, 5.38, places=2)
        
        # At half coherence
        reduction_half = calculate_mass_reduction(0.5)
        self.assertAlmostEqual(reduction_half, 2.69, places=2)
        
        # At zero coherence
        reduction_0 = calculate_mass_reduction(0.0)
        self.assertEqual(reduction_0, 0.0)


def run_tests():
    """Run all tests with formatted output."""
    print("=" * 70)
    print("Fermion-Higgs Lagrangian P=NP Framework Tests")
    print("ℒ_int = -g_eff ψ ψ̄ H")
    print(f"∴𓂀Ω∞³ | f₀ = {F0_HZ} Hz | T₀ = {T0_MS:.4f} ms")
    print("=" * 70)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    test_classes = [
        TestPhysicalConstants,
        TestHiggsParameters,
        TestFermionState,
        TestFermionHiggsLagrangian,
        TestQuantumCoherenceField,
        TestFermionHiggsNPOracle,
        TestCabelloUnit,
        TestParallelConfigurationExplorer,
        TestBerryState,
        TestParameterPath,
        TestBerryPhaseCalculator,
        TestBerryPhaseOracle,
        TestIntegratedBerryHiggsOracle,
        TestUtilityFunctions
    ]
    
    for test_class in test_classes:
        suite.addTests(loader.loadTestsFromTestCase(test_class))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Summary
    print()
    print("=" * 70)
    if result.wasSuccessful():
        print("✓ All tests passed!")
        print(f"  Total tests: {result.testsRun}")
    else:
        print("✗ Some tests failed")
        print(f"  Total tests: {result.testsRun}")
        print(f"  Failures: {len(result.failures)}")
        print(f"  Errors: {len(result.errors)}")
    print("=" * 70)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
