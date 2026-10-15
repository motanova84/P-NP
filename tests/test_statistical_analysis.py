"""
Unit tests for statistical analysis module

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os
import json
import tempfile
import shutil
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from experiments.statistical_analysis import StatisticalAnalyzer, NumpyEncoder
import numpy as np


class TestNumpyEncoder(unittest.TestCase):
    """Test cases for NumpyEncoder."""
    
    def test_encode_numpy_int(self):
        """Test encoding numpy integer."""
        data = {'value': np.int64(42)}
        result = json.dumps(data, cls=NumpyEncoder)
        self.assertIn('42', result)
    
    def test_encode_numpy_float(self):
        """Test encoding numpy float."""
        data = {'value': np.float64(3.14)}
        result = json.dumps(data, cls=NumpyEncoder)
        self.assertIn('3.14', result)
    
    def test_encode_numpy_bool(self):
        """Test encoding numpy bool."""
        data = {'value': np.bool_(True)}
        result = json.dumps(data, cls=NumpyEncoder)
        self.assertIn('true', result)
    
    def test_encode_numpy_array(self):
        """Test encoding numpy array."""
        data = {'values': np.array([1, 2, 3])}
        result = json.dumps(data, cls=NumpyEncoder)
        self.assertIn('[1, 2, 3]', result)


class TestStatisticalAnalyzer(unittest.TestCase):
    """Test cases for StatisticalAnalyzer class."""
    
    @classmethod
    def setUpClass(cls):
        """Set up test fixtures."""
        cls.test_dir = tempfile.mkdtemp()
        cls.test_data_file = os.path.join(cls.test_dir, 'test_validation.json')
        
        # Create test data
        test_data = {
            "metadata": {
                "description": "Test data for statistical analysis",
                "version": "1.0"
            },
            "results": [
                {
                    "n": 10,
                    "n_vars": 10,
                    "n_clauses": 20,
                    "treewidth": 2.5,
                    "information_complexity": 3.2,
                    "time_dpll": 0.05,
                    "solved_dpll": True,
                    "algorithms": {
                        "cdcl": {"time": 0.04, "solved": True},
                        "walksat": {"time": 0.06, "solved": True}
                    }
                },
                {
                    "n": 20,
                    "n_vars": 20,
                    "n_clauses": 40,
                    "treewidth": 3.8,
                    "information_complexity": 5.1,
                    "time_dpll": 0.15,
                    "solved_dpll": True,
                    "algorithms": {
                        "cdcl": {"time": 0.12, "solved": True},
                        "walksat": {"time": 0.18, "solved": True}
                    }
                },
                {
                    "n": 30,
                    "n_vars": 30,
                    "n_clauses": 60,
                    "treewidth": 5.2,
                    "information_complexity": 7.8,
                    "time_dpll": 0.45,
                    "solved_dpll": True,
                    "algorithms": {
                        "cdcl": {"time": 0.38, "solved": True},
                        "walksat": {"time": 0.52, "solved": True}
                    }
                },
                {
                    "n": 40,
                    "n_vars": 40,
                    "n_clauses": 80,
                    "treewidth": 6.9,
                    "information_complexity": 11.2,
                    "time_dpll": 1.25,
                    "solved_dpll": True,
                    "algorithms": {
                        "cdcl": {"time": 1.05, "solved": True},
                        "walksat": {"time": 1.45, "solved": True}
                    }
                },
                {
                    "n": 50,
                    "n_vars": 50,
                    "n_clauses": 100,
                    "treewidth": 8.6,
                    "information_complexity": 15.3,
                    "time_dpll": 3.85,
                    "solved_dpll": True,
                    "algorithms": {
                        "cdcl": {"time": 3.25, "solved": True},
                        "walksat": {"time": 4.45, "solved": True}
                    }
                }
            ]
        }
        
        with open(cls.test_data_file, 'w') as f:
            json.dump(test_data, f)
    
    @classmethod
    def tearDownClass(cls):
        """Clean up test fixtures."""
        shutil.rmtree(cls.test_dir)
    
    def test_load_data(self):
        """Test loading validation data."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        self.assertEqual(len(analyzer.df), 5)
        self.assertIn('treewidth', analyzer.df.columns)
        self.assertIn('information_complexity', analyzer.df.columns)
        self.assertIn('time_dpll', analyzer.df.columns)
    
    def test_analyze_correlations(self):
        """Test correlation analysis."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        correlations = analyzer.analyze_correlations()
        
        self.assertIn('pearson', correlations)
        self.assertIn('spearman', correlations)
        self.assertIn('partial', correlations)
        
        # Check that correlations are in valid range
        pearson = correlations['pearson']
        for var1 in pearson:
            for var2 in pearson[var1]:
                corr = pearson[var1][var2]
                self.assertGreaterEqual(corr, -1.0)
                self.assertLessEqual(corr, 1.0)
    
    def test_exponential_hypothesis(self):
        """Test exponential time hypothesis testing."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        results = analyzer.test_exponential_hypothesis()
        
        self.assertIn('model_comparison', results)
        self.assertIn('exponential', results['model_comparison'])
        self.assertIn('linear', results['model_comparison'])
        self.assertIn('quadratic', results['model_comparison'])
    
    def test_no_evasion_hypothesis(self):
        """Test no-evasion hypothesis testing."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        results = analyzer.test_no_evasion_hypothesis()
        
        # Should have algorithm comparison results
        self.assertIn('friedman_test', results)
        self.assertIn('pairwise_comparisons', results)
        self.assertIn('performance_summary', results)
    
    def test_growth_rates(self):
        """Test growth rate analysis."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        results = analyzer.analyze_growth_rates()
        
        # Should have growth rates for key metrics
        self.assertIn('treewidth', results)
        self.assertIn('information_complexity', results)
        self.assertIn('time_dpll', results)
        
        # Check that exponents are positive
        for metric in results:
            self.assertIn('exponent', results[metric])
            self.assertIn('r_squared', results[metric])
    
    def test_calculate_r_squared(self):
        """Test R-squared calculation."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        
        y_true = np.array([1, 2, 3, 4, 5])
        y_pred = np.array([1.1, 2.0, 2.9, 4.1, 5.0])
        
        r_squared = analyzer._calculate_r_squared(y_true, y_pred)
        
        # Should be close to 1 for good fit
        self.assertGreater(r_squared, 0.95)
        self.assertLessEqual(r_squared, 1.0)
    
    def test_get_residuals(self):
        """Test residual calculation."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        
        x = analyzer.df['n']
        y = analyzer.df['treewidth']
        
        residuals = analyzer._get_residuals(y, x)
        
        # Residuals should have same length as input
        self.assertEqual(len(residuals), len(x))
        
        # Mean of residuals should be close to zero
        self.assertAlmostEqual(np.mean(residuals), 0, places=10)
    
    def test_comprehensive_report(self):
        """Test comprehensive report generation."""
        analyzer = StatisticalAnalyzer(self.test_data_file)
        
        output_dir = os.path.join(self.test_dir, 'test_output')
        report = analyzer.generate_comprehensive_report(output_dir)
        
        # Check that report contains all sections
        self.assertIn('correlation_analysis', report)
        self.assertIn('exponential_hypothesis', report)
        self.assertIn('no_evasion_test', report)
        self.assertIn('growth_rate_analysis', report)
        self.assertIn('descriptive_statistics', report)
        
        # Check that files were created
        self.assertTrue(os.path.exists(os.path.join(output_dir, 'statistical_report.json')))
        self.assertTrue(os.path.exists(os.path.join(output_dir, 'statistical_analysis.png')))
        
        # Clean up
        shutil.rmtree(output_dir)


if __name__ == '__main__':
    unittest.main()
