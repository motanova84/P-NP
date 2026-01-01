"""
Unit tests for Block 9 synchronization analysis with QCAL ∞³ frequency

Author: P-NP Verification System
"""

import unittest
import sys
import os
import json
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Import the analyzer after adding parent to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'echo_qcal'))
from block9_sync_analysis import Block9SyncAnalyzer


class TestBlock9SyncAnalyzer(unittest.TestCase):
    """Test cases for Block 9 synchronization analyzer."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.analyzer = Block9SyncAnalyzer()
    
    def test_qcal_parameters(self):
        """Test that QCAL ∞³ parameters are correctly initialized."""
        self.assertEqual(self.analyzer.f0, 141.7001)
        self.assertAlmostEqual(self.analyzer.tau0, 1 / 141.7001, places=10)
        self.assertEqual(self.analyzer.T_block9, 1231511700.000000)
    
    def test_calculate_sync_metrics(self):
        """Test that sync metrics are calculated correctly."""
        metrics = self.analyzer.calculate_sync_metrics()
        
        # Check that all required keys are present
        required_keys = [
            'delta_T_ms', 'delta_T_seconds', 'coherence_percent',
            'p_value', 'bayes_factor', 'z_score', 'N_multiplier',
            'T_ideal', 'T_actual', 'tau0', 'f0'
        ]
        for key in required_keys:
            self.assertIn(key, metrics)
        
        # Check reasonable ranges
        self.assertGreater(metrics['coherence_percent'], 0)
        self.assertLess(metrics['coherence_percent'], 100)
        self.assertGreater(metrics['p_value'], 0)
        self.assertGreater(metrics['bayes_factor'], 0)
        self.assertGreater(metrics['N_multiplier'], 0)
    
    def test_statistical_significance(self):
        """Test statistical significance evaluation."""
        metrics = self.analyzer.calculate_sync_metrics()
        significance = self.analyzer.statistical_significance(metrics)
        
        # Check that all required keys are present
        required_keys = ['significant', 'highly_significant', 
                        'extremely_significant', 'interpretation']
        for key in required_keys:
            self.assertIn(key, significance)
        
        # Check that interpretation is a non-empty string
        self.assertIsInstance(significance['interpretation'], str)
        self.assertGreater(len(significance['interpretation']), 0)
    
    def test_generate_report(self):
        """Test report generation."""
        # Generate report without saving
        report = self.analyzer.generate_report(save_path=None)
        
        # Check required top-level keys
        required_keys = [
            'analysis_timestamp', 'block9_timestamp', 'block9_datetime',
            'qcal_parameters', 'sync_metrics', 'statistical_significance',
            'conclusions'
        ]
        for key in required_keys:
            self.assertIn(key, report)
        
        # Check QCAL parameters
        self.assertEqual(report['qcal_parameters']['f0'], 141.7001)
        self.assertEqual(report['qcal_parameters']['source'], 'QCAL ∞³ Framework')
        
        # Check conclusions
        self.assertIsInstance(report['conclusions'], list)
    
    def test_report_json_serializable(self):
        """Test that report can be serialized to JSON."""
        report = self.analyzer.generate_report(save_path=None)
        
        # Should not raise an exception
        try:
            json_str = json.dumps(report, indent=2)
            self.assertIsInstance(json_str, str)
        except Exception as e:
            self.fail(f"Report is not JSON serializable: {e}")
    
    def test_p_value_calculation(self):
        """Test that p-value is calculated correctly."""
        metrics = self.analyzer.calculate_sync_metrics()
        
        # p_value = (2 * epsilon) / window
        expected_p_value = (2 * self.analyzer.epsilon) / self.analyzer.window
        self.assertAlmostEqual(metrics['p_value'], expected_p_value, places=10)
    
    def test_bayes_factor_calculation(self):
        """Test that Bayes factor is calculated correctly."""
        metrics = self.analyzer.calculate_sync_metrics()
        
        # bayes_factor = window / (2 * epsilon)
        expected_bayes_factor = self.analyzer.window / (2 * self.analyzer.epsilon)
        self.assertAlmostEqual(metrics['bayes_factor'], expected_bayes_factor, places=10)
    
    def test_coherence_calculation(self):
        """Test that coherence is calculated correctly."""
        metrics = self.analyzer.calculate_sync_metrics()
        
        # coherence = (1 - delta_T / tau0) * 100
        coherence = (1 - metrics['delta_T_seconds'] / self.analyzer.tau0) * 100
        self.assertAlmostEqual(metrics['coherence_percent'], coherence, places=6)
    
    def test_block9_timestamp_accuracy(self):
        """Test that Block 9 timestamp is exact."""
        # Block 9 was mined on 2009-01-09 17:15:00 UTC
        # Unix timestamp: 1231511700
        self.assertEqual(self.analyzer.T_block9, 1231511700.0)
    
    def test_synchronization_threshold(self):
        """Test that synchronization is within threshold."""
        metrics = self.analyzer.calculate_sync_metrics()
        
        # delta_T should be less than epsilon (10 ms)
        self.assertLess(metrics['delta_T_seconds'], self.analyzer.epsilon)


class TestBlock9SyncAnalyzerExecution(unittest.TestCase):
    """Test that the analyzer script executes correctly."""
    
    def test_script_runs(self):
        """Test that the script runs without errors."""
        import subprocess
        
        result = subprocess.run(
            ['python3', 'echo_qcal/block9_sync_analysis.py'],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        # Should complete successfully
        self.assertEqual(result.returncode, 0)
        
        # Should contain key output markers
        self.assertIn('QCAL ∞³', result.stdout)
        self.assertIn('Bloque 9', result.stdout)
        self.assertIn('Análisis completado exitosamente', result.stdout)
    
    def test_output_files_created(self):
        """Test that output files are created."""
        # Run the script
        import subprocess
        
        subprocess.run(
            ['python3', 'echo_qcal/block9_sync_analysis.py'],
            capture_output=True,
            timeout=30
        )
        
        # Check that JSON report was created
        json_path = Path('data/block9_sync_report.json')
        self.assertTrue(json_path.exists())
        
        # Check that diagram was created
        diagram_path = Path('diagrams/block9_sync_analysis.png')
        self.assertTrue(diagram_path.exists())


if __name__ == '__main__':
    print("Running Block 9 Synchronization Tests ∞³")
    print("QCAL ∞³ Frequency: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
