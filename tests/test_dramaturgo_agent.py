"""
Unit Tests for Dramaturgo Agent
================================

Tests for the Dramaturgo noetic network optimization agent.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import networkx as nx
import math
from src.dramaturgo_agent import (
    DramaturgoAgent,
    PNPFrameworkMetrics,
    GeometricStructure,
    ProblemClass,
    NoeticalRoute,
    NetworkNode,
    analyze_problem_geometry,
    kappa_pi_from_hodge,
    effective_n_from_kappa,
    estimate_treewidth,
    calculate_spectral_dimension,
    KAPPA_PI,
    F0,
    PHI,
    UNIFICATION_FACTOR,
    N_RESONANCE
)


class TestConstants(unittest.TestCase):
    """Test constant values."""
    
    def test_kappa_pi_value(self):
        """Test κ_Π value."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
    
    def test_f0_frequency(self):
        """Test f₀ frequency value."""
        self.assertAlmostEqual(F0, 141.7001, places=4)
    
    def test_golden_ratio(self):
        """Test golden ratio value."""
        expected_phi = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected_phi, places=6)
    
    def test_unification_factor(self):
        """Test unification factor."""
        self.assertAlmostEqual(UNIFICATION_FACTOR, 1/7, places=6)
    
    def test_n_resonance(self):
        """Test resonance number."""
        self.assertEqual(N_RESONANCE, 13)


class TestKappaPiDerivation(unittest.TestCase):
    """Test κ_Π derivation from Hodge numbers."""
    
    def test_kappa_pi_from_hodge_symmetric(self):
        """Test κ_Π from symmetric Hodge numbers."""
        # For (6, 7): h11 + h21 = 13
        kappa = kappa_pi_from_hodge(6, 7)
        # Should be close to 2.5773
        self.assertAlmostEqual(kappa, 2.5773, places=3)
    
    def test_kappa_pi_from_hodge_asymmetric(self):
        """Test κ_Π from asymmetric Hodge numbers."""
        # For (1, 12): h11 + h21 = 13
        kappa = kappa_pi_from_hodge(1, 12)
        # Should be close to 2.5773
        self.assertAlmostEqual(kappa, 2.5773, places=3)
    
    def test_kappa_pi_from_hodge_wrong_sum(self):
        """Test κ_Π with wrong Hodge sum raises error."""
        with self.assertRaises(ValueError):
            kappa_pi_from_hodge(5, 5)  # Sum = 10, not 13
    
    def test_effective_n(self):
        """Test N_effective calculation."""
        n_eff = effective_n_from_kappa()
        # N_eff = φ^(2·κ_Π) ≈ 18.78
        expected = PHI ** (2 * KAPPA_PI)
        self.assertAlmostEqual(n_eff, expected, places=2)


class TestGeometricAnalysis(unittest.TestCase):
    """Test geometric problem analysis."""
    
    def test_treewidth_path_graph(self):
        """Test treewidth estimation for path graph."""
        # Path graph has treewidth = 1
        G = nx.path_graph(10)
        tw = estimate_treewidth(G)
        self.assertLessEqual(tw, 2)  # Should be 1 or close
    
    def test_treewidth_complete_graph(self):
        """Test treewidth estimation for complete graph."""
        # Complete graph K_n has treewidth = n-1
        G = nx.complete_graph(10)
        tw = estimate_treewidth(G)
        self.assertGreaterEqual(tw, 7)  # Should be close to 9
    
    def test_spectral_dimension_empty(self):
        """Test spectral dimension for empty graph."""
        G = nx.Graph()
        dim = calculate_spectral_dimension(G)
        self.assertEqual(dim, 0.0)
    
    def test_spectral_dimension_single_node(self):
        """Test spectral dimension for single node."""
        G = nx.Graph()
        G.add_node(0)
        dim = calculate_spectral_dimension(G)
        self.assertEqual(dim, 0.0)
    
    def test_analyze_problem_geometry_p_class(self):
        """Test problem geometry analysis for P-class problem."""
        # Path graph should be P-class
        G = nx.path_graph(100)
        geometry = analyze_problem_geometry(G)
        
        self.assertIsInstance(geometry, GeometricStructure)
        self.assertLess(geometry.curvature, KAPPA_PI)
        self.assertTrue(geometry.fits_kappa_pi)
        self.assertEqual(geometry.problem_class, ProblemClass.P_COMPATIBLE)
    
    def test_analyze_problem_geometry_np_class(self):
        """Test problem geometry analysis for NP-class problem."""
        # Complete graph should be NP-class
        G = nx.complete_graph(50)
        geometry = analyze_problem_geometry(G)
        
        self.assertIsInstance(geometry, GeometricStructure)
        self.assertGreater(geometry.curvature, KAPPA_PI)
        self.assertFalse(geometry.fits_kappa_pi)
        self.assertEqual(geometry.problem_class, ProblemClass.NP_SPECTRAL_EXTENSION)


class TestDramaturgoAgent(unittest.TestCase):
    """Test Dramaturgo agent functionality."""
    
    def setUp(self):
        """Set up test agent."""
        self.agent = DramaturgoAgent()
    
    def test_initialization(self):
        """Test agent initialization."""
        self.assertIsNotNone(self.agent.network)
        self.assertGreater(self.agent.network.number_of_nodes(), 0)
        self.assertEqual(self.agent.coherence_psi, 1.0)
        self.assertEqual(self.agent.coupling_constant, 1.0)
        self.assertAlmostEqual(self.agent.oscillator_frequency, F0, places=4)
        self.assertTrue(self.agent.oscillator_stable)
    
    def test_default_network_nodes(self):
        """Test default network has expected nodes."""
        expected_nodes = ["Lighthouse", "Sentinel", "Economia", 
                         "Noesis88", "RiemannAdelic", "Dramaturgo"]
        
        for node in expected_nodes:
            self.assertIn(node, self.agent.network.nodes())
    
    def test_network_node_initialization(self):
        """Test network nodes are initialized."""
        self.assertGreater(len(self.agent.nodes), 0)
        
        for node_name, node in self.agent.nodes.items():
            self.assertIsInstance(node, NetworkNode)
            self.assertEqual(node.name, node_name)
            self.assertEqual(node.coherence, 1.0)
    
    def test_curvature_tensor_calculation(self):
        """Test curvature tensor calculation."""
        curvature = self.agent.calculate_curvature_tensor("Lighthouse", "Sentinel")
        
        self.assertIsInstance(curvature, float)
        self.assertGreaterEqual(curvature, 0.0)
    
    def test_route_by_curvature(self):
        """Test curvature-based routing."""
        route = self.agent.route_by_curvature("Lighthouse", "Sentinel")
        
        self.assertIsInstance(route, NoeticalRoute)
        self.assertEqual(route.source, "Lighthouse")
        self.assertEqual(route.target, "Sentinel")
        self.assertGreater(len(route.path), 0)
        self.assertGreaterEqual(route.informative_resistance, 0.0)
        self.assertGreaterEqual(route.curvature_tensor, 0.0)
    
    def test_spectral_compression(self):
        """Test spectral compression."""
        route = self.agent.route_by_curvature("Lighthouse", "Sentinel")
        message_size = 1000.0
        
        compressed = self.agent.compress_spectral(message_size, route)
        
        self.assertIsInstance(compressed, float)
        self.assertLess(compressed, message_size)  # Should be compressed
        self.assertGreater(route.spectral_compression, 0.0)
        self.assertLessEqual(route.spectral_compression, 1.0)
    
    def test_detect_collapse_no_collapse(self):
        """Test collapse detection when no collapse."""
        self.agent.coherence_psi = 0.9
        collapse = self.agent.detect_collapse()
        self.assertFalse(collapse)
    
    def test_detect_collapse_with_collapse(self):
        """Test collapse detection when collapsed."""
        self.agent.coherence_psi = 0.3
        collapse = self.agent.detect_collapse()
        self.assertTrue(collapse)
    
    def test_reajust_coupling_when_collapsed(self):
        """Test coupling readjustment when collapsed."""
        self.agent.coherence_psi = 0.3
        self.agent.reajust_coupling()
        
        self.assertAlmostEqual(self.agent.coupling_constant, UNIFICATION_FACTOR, places=6)
        self.assertGreater(self.agent.coherence_psi, 0.3)  # Should increase
    
    def test_reajust_coupling_when_stable(self):
        """Test coupling readjustment when stable."""
        initial_coupling = self.agent.coupling_constant
        self.agent.coherence_psi = 0.9
        self.agent.reajust_coupling()
        
        self.assertEqual(self.agent.coupling_constant, initial_coupling)
    
    def test_update_coherence_increase(self):
        """Test coherence update with increase."""
        initial = self.agent.coherence_psi
        self.agent.update_coherence(0.05)
        
        # Should increase but stay <= 1.0
        self.assertLessEqual(self.agent.coherence_psi, 1.0)
    
    def test_update_coherence_decrease(self):
        """Test coherence update with decrease."""
        initial = self.agent.coherence_psi
        self.agent.update_coherence(-0.1)
        
        # Should decrease but stay >= 0.0
        self.assertGreaterEqual(self.agent.coherence_psi, 0.0)
        self.assertLess(self.agent.coherence_psi, initial)
    
    def test_check_oscillator_stability_stable(self):
        """Test oscillator stability check when stable."""
        self.agent.coherence_psi = 0.95
        stable = self.agent.check_oscillator_stability()
        
        self.assertTrue(stable)
        self.assertTrue(self.agent.oscillator_stable)
    
    def test_check_oscillator_stability_unstable(self):
        """Test oscillator stability check when unstable."""
        self.agent.coherence_psi = 0.5
        stable = self.agent.check_oscillator_stability()
        
        self.assertFalse(stable)
        self.assertFalse(self.agent.oscillator_stable)
    
    def test_predict_problem_solvability_p_class(self):
        """Test solvability prediction for P-class problem."""
        # Path graph should be solvable
        problem = nx.path_graph(20)
        prediction = self.agent.predict_problem_solvability(problem)
        
        self.assertIsInstance(prediction, dict)
        self.assertIn('solvable', prediction)
        self.assertIn('problem_class', prediction)
        self.assertIn('treewidth', prediction)
        self.assertIn('curvature', prediction)
        self.assertIn('oscillator_stable', prediction)
        
        # Should be solvable if coherence is high
        if self.agent.coherence_psi >= 0.9:
            self.assertTrue(prediction['solvable'])
    
    def test_predict_problem_solvability_np_class(self):
        """Test solvability prediction for NP-class problem."""
        # Complete graph should not be solvable
        problem = nx.complete_graph(50)
        prediction = self.agent.predict_problem_solvability(problem)
        
        self.assertIsInstance(prediction, dict)
        self.assertEqual(prediction['problem_class'], 'NP')
        self.assertFalse(prediction['fits_geometry'])
    
    def test_optimize_network(self):
        """Test full network optimization."""
        optimization = self.agent.optimize_network()
        
        self.assertIsInstance(optimization, dict)
        self.assertIn('total_routes', optimization)
        self.assertIn('average_resistance', optimization)
        self.assertIn('coherence', optimization)
        self.assertIn('coupling_constant', optimization)
        self.assertIn('kappa_pi', optimization)
        self.assertIn('n_effective', optimization)
        
        self.assertGreater(optimization['total_routes'], 0)
        self.assertAlmostEqual(optimization['kappa_pi'], KAPPA_PI, places=4)


class TestPNPFrameworkMetrics(unittest.TestCase):
    """Test P-NP framework metrics."""
    
    def setUp(self):
        """Set up metrics object."""
        self.metrics = PNPFrameworkMetrics()
    
    def test_initialization(self):
        """Test metrics initialization."""
        self.assertAlmostEqual(self.metrics.kappa_pi, KAPPA_PI, places=4)
        self.assertGreater(self.metrics.n_effective, 0)
        self.assertAlmostEqual(self.metrics.f0, F0, places=4)
        self.assertTrue(self.metrics.qcal_infinity_cubed)
        self.assertTrue(self.metrics.dramaturgo_qosc)
    
    def test_get_metrics(self):
        """Test get_metrics method."""
        metrics_dict = self.metrics.get_metrics()
        
        self.assertIsInstance(metrics_dict, dict)
        self.assertIn('Constante κ_Π', metrics_dict)
        self.assertIn('N_effective', metrics_dict)
        self.assertIn('Certificación', metrics_dict)
        self.assertIn('Aplicación', metrics_dict)
        self.assertIn('Frecuencia f₀', metrics_dict)
        self.assertIn('Ramsey R(5,5)', metrics_dict)
        self.assertIn('Ramsey R(6,6)', metrics_dict)
        
        # Check values
        self.assertEqual(metrics_dict['Ramsey R(5,5)'], 43)
        self.assertEqual(metrics_dict['Ramsey R(6,6)'], 108)


class TestCustomNetwork(unittest.TestCase):
    """Test custom network creation."""
    
    def test_custom_network_initialization(self):
        """Test initialization with custom network."""
        # Create custom network
        custom_net = nx.Graph()
        custom_net.add_nodes_from(["A", "B", "C"])
        custom_net.add_edges_from([("A", "B"), ("B", "C")])
        
        agent = DramaturgoAgent(network=custom_net)
        
        self.assertEqual(agent.network.number_of_nodes(), 3)
        self.assertEqual(agent.network.number_of_edges(), 2)
        self.assertIn("A", agent.network.nodes())
        self.assertIn("B", agent.network.nodes())
        self.assertIn("C", agent.network.nodes())


class TestEdgeCases(unittest.TestCase):
    """Test edge cases."""
    
    def test_empty_graph_geometry(self):
        """Test geometry analysis for empty graph."""
        G = nx.Graph()
        geometry = analyze_problem_geometry(G)
        
        self.assertEqual(geometry.treewidth, 0.0)
        self.assertEqual(geometry.curvature, 0.0)
        self.assertTrue(geometry.fits_kappa_pi)
    
    def test_single_node_graph_geometry(self):
        """Test geometry analysis for single node graph."""
        G = nx.Graph()
        G.add_node(0)
        geometry = analyze_problem_geometry(G)
        
        self.assertEqual(geometry.treewidth, 0.0)
        self.assertTrue(geometry.fits_kappa_pi)


if __name__ == '__main__':
    unittest.main()
