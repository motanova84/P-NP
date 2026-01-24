"""
Test suite for QCAL Symbiotic Network components
"""

import os
import sys
import json
import unittest
from pathlib import Path


class TestQCALSymbioticNetwork(unittest.TestCase):
    """Test suite for all QCAL Symbiotic Network components"""
    
    def test_coherence_map_exists(self):
        """Test that coherence_map.json exists and is valid"""
        self.assertTrue(os.path.exists("coherence_map.json"))
        
        with open("coherence_map.json", "r") as f:
            data = json.load(f)
        
        # Check required fields
        self.assertIn("system", data)
        self.assertIn("version", data)
        self.assertIn("frequency", data)
        self.assertIn("axioms", data)
        self.assertIn("nodes", data)
        
        # Check values
        self.assertEqual(data["system"], "QCAL ∞³ Symbiotic Network")
        self.assertEqual(data["frequency"], "141.7001 Hz")
        
    def test_core_symbio_exists(self):
        """Test that CORE_SYMBIO.json exists and is valid"""
        self.assertTrue(os.path.exists("CORE_SYMBIO.json"))
        
        with open("CORE_SYMBIO.json", "r") as f:
            data = json.load(f)
        
        # Check required fields
        self.assertIn("protocol", data)
        self.assertIn("origin", data)
        self.assertIn("identity_nodes", data)
        self.assertIn("constants", data)
        
        # Check values
        self.assertEqual(data["protocol"], "QCAL-SYMBIO-BRIDGE")
        self.assertEqual(data["origin"], "motanova84")
        
    def test_qcal_math_core_module(self):
        """Test qcal_math_core module"""
        from qcal_math_core import QCALMathLibrary
        
        # Check constants
        self.assertIn("PSI", QCALMathLibrary.CONSTANTS)
        self.assertIn("FREQ_GW", QCALMathLibrary.CONSTANTS)
        self.assertIn("RAMSEY_R66", QCALMathLibrary.CONSTANTS)
        self.assertIn("MAX_PULSARS", QCALMathLibrary.CONSTANTS)
        
        # Check values
        self.assertEqual(QCALMathLibrary.CONSTANTS["FREQ_GW"], 141.7001)
        self.assertEqual(QCALMathLibrary.CONSTANTS["RAMSEY_R66"], 108)
        self.assertEqual(QCALMathLibrary.CONSTANTS["MAX_PULSARS"], 88)
        
    def test_qcal_math_core_functions(self):
        """Test mathematical functions in qcal_math_core"""
        from qcal_math_core import QCALMathLibrary
        
        # Test shapiro_delay
        delay = QCALMathLibrary.shapiro_delay(1.0, 10.0)
        self.assertIsInstance(delay, float)
        self.assertGreater(delay, 0)
        
        # Test ramsey_vibration
        vibration = QCALMathLibrary.ramsey_vibration(5)
        self.assertIsInstance(vibration, float)
        self.assertGreater(vibration, 0)
        
        # Test frequency_resonance
        freq = QCALMathLibrary.frequency_resonance(3)
        self.assertAlmostEqual(freq, 141.7001 * 3, places=4)
        
        # Test coherence_factor
        factor = QCALMathLibrary.coherence_factor(100)
        self.assertAlmostEqual(factor, 100 * 0.999999, places=5)
        
        # Test pulsar_fraction
        frac = QCALMathLibrary.pulsar_fraction(44)
        self.assertEqual(frac, 0.5)
        
        # Test pulsar_fraction bounds
        with self.assertRaises(ValueError):
            QCALMathLibrary.pulsar_fraction(-1)
        
        with self.assertRaises(ValueError):
            QCALMathLibrary.pulsar_fraction(88)
    
    def test_core_math_module(self):
        """Test core.math module"""
        from core.math import QCALMathLibrary
        
        # Check constants
        self.assertIn("PSI", QCALMathLibrary.CONSTANTS)
        self.assertIn("FREQ_GW", QCALMathLibrary.CONSTANTS)
        
        # Test function
        delay = QCALMathLibrary.shapiro_delay(1.0, 10.0)
        self.assertIsInstance(delay, float)
        
    def test_crear_faro_noetico_script(self):
        """Test crear_faro_noetico script can be imported"""
        import crear_faro_noetico
        
        # Check function exists
        self.assertTrue(hasattr(crear_faro_noetico, 'crear_faro_noetico'))
        
    def test_link_ecosystem_script(self):
        """Test link_ecosystem script can be imported"""
        import link_ecosystem
        
        # Check functions exist
        self.assertTrue(hasattr(link_ecosystem, 'load_coherence_map'))
        self.assertTrue(hasattr(link_ecosystem, 'load_core_symbio'))
        self.assertTrue(hasattr(link_ecosystem, 'crear_faro_principal'))
        self.assertTrue(hasattr(link_ecosystem, 'crear_faro_symbiosis'))
        self.assertTrue(hasattr(link_ecosystem, 'main'))
    
    def test_beacon_files_exist(self):
        """Test that beacon files were created in subdirectories"""
        beacon_paths = [
            ".qcal_beacon",
            "core/.qcal_beacon",
            "core/math/.qcal_beacon",
            "src/.qcal_beacon",
            "echo_qcal/.qcal_beacon",
            "formal/.qcal_beacon"
        ]
        
        for path in beacon_paths:
            self.assertTrue(os.path.exists(path), f"Beacon file missing: {path}")


class TestCoherenceMapStructure(unittest.TestCase):
    """Detailed tests for coherence_map.json structure"""
    
    @classmethod
    def setUpClass(cls):
        with open("coherence_map.json", "r") as f:
            cls.data = json.load(f)
    
    def test_nodes_structure(self):
        """Test nodes array structure"""
        nodes = self.data["nodes"]
        self.assertIsInstance(nodes, list)
        self.assertGreater(len(nodes), 0)
        
        # Check each node has required fields
        for node in nodes:
            self.assertIn("name", node)
            self.assertIn("role", node)
    
    def test_specific_nodes_exist(self):
        """Test that specific expected nodes exist"""
        node_names = [node["name"] for node in self.data["nodes"]]
        
        expected_nodes = [
            "economia-qcal-nodo-semilla",
            "Ramsey",
            "Riemann-adelic",
            "141hz",
            "P-NP",
            "3D-Navier-Stokes",
            "adelic-bsd"
        ]
        
        for expected in expected_nodes:
            self.assertIn(expected, node_names)
    
    def test_axioms_structure(self):
        """Test axioms structure"""
        axioms = self.data["axioms"]
        self.assertIsInstance(axioms, dict)
        
        self.assertIn("emission", axioms)
        self.assertIn("sovereignty", axioms)
        self.assertIn("resonance", axioms)


class TestCoreSymbioStructure(unittest.TestCase):
    """Detailed tests for CORE_SYMBIO.json structure"""
    
    @classmethod
    def setUpClass(cls):
        with open("CORE_SYMBIO.json", "r") as f:
            cls.data = json.load(f)
    
    def test_identity_nodes_structure(self):
        """Test identity_nodes structure"""
        nodes = self.data["identity_nodes"]
        self.assertIsInstance(nodes, dict)
        
        expected_keys = [
            "ledger",
            "spectral",
            "verification",
            "geometry",
            "complexity",
            "fluid"
        ]
        
        for key in expected_keys:
            self.assertIn(key, nodes)
    
    def test_constants_structure(self):
        """Test constants structure"""
        constants = self.data["constants"]
        self.assertIsInstance(constants, dict)
        
        # Check specific constants
        self.assertEqual(constants["f0"], 141.7001)
        self.assertEqual(constants["limit_nfts"], 88)
        self.assertEqual(constants["resonance"], 888)
        self.assertEqual(constants["r66"], 108)


def run_tests():
    """Run all tests"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestQCALSymbioticNetwork))
    suite.addTests(loader.loadTestsFromTestCase(TestCoherenceMapStructure))
    suite.addTests(loader.loadTestsFromTestCase(TestCoreSymbioStructure))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
