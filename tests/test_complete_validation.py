"""
Tests for Complete Experimental Validation

Tests the complete validation framework including:
- Hard instance generation
- Treewidth estimation
- Information complexity computation
- Solver wrappers
- Statistical analysis
"""

import pytest
import numpy as np
import networkx as nx
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from experiments.complete_validation import (
    CompleteValidation,
    ICSATSolver,
    DPLLSolver,
    generate_tseitin_expander
)
from src.computational_dichotomy import CNFFormula


class TestTseitinGeneration:
    """Test Tseitin formula generation."""
    
    def test_generate_tseitin_expander_small(self):
        """Test generating Tseitin formula over small expander."""
        G = nx.random_regular_graph(3, 6)
        phi = generate_tseitin_expander(G)
        
        # Check it's a CNFFormula-like object
        assert hasattr(phi, 'num_vars')
        assert hasattr(phi, 'clauses')
        assert phi.num_vars > 0
        assert len(phi.clauses) > 0
    
    def test_generate_tseitin_expander_medium(self):
        """Test generating Tseitin formula over medium expander."""
        G = nx.random_regular_graph(3, 20)
        phi = generate_tseitin_expander(G)
        
        # Check it's a CNFFormula-like object
        assert hasattr(phi, 'num_vars')
        assert hasattr(phi, 'clauses')
        assert phi.num_vars == len(G.edges())
        assert len(phi.clauses) > 0


class TestSolverWrappers:
    """Test solver wrapper classes."""
    
    def test_icsat_solver_wrapper(self):
        """Test ICSATSolver wrapper."""
        # Create simple formula
        formula = CNFFormula(3, [[1, 2], [-1, 3], [2, -3]])
        solver = ICSATSolver(formula)
        
        assert solver.n_vars == 3
        assert len(solver.clauses) == 3
        
        # Solve
        result = solver.solve(track_ic=True)
        assert 'satisfiable' in result
        assert 'information_complexity' in result
        assert isinstance(result['information_complexity'], float)
    
    def test_dpll_solver_wrapper(self):
        """Test DPLLSolver wrapper."""
        # Create simple satisfiable formula
        formula = CNFFormula(2, [[1, 2], [-1, 2]])
        solver = DPLLSolver(formula)
        
        assert solver.n_vars == 2
        assert len(solver.clauses) == 2
        
        # Solve
        result = solver.solve(timeout=10)
        assert 'satisfiable' in result
        assert 'time' in result
        assert result['satisfiable'] is True


class TestCompleteValidation:
    """Test CompleteValidation class."""
    
    def test_initialization(self):
        """Test validator initialization."""
        validator = CompleteValidation(n_min=10, n_max=20, n_step=5)
        
        assert validator.n_min == 10
        assert validator.n_max == 20
        assert validator.n_step == 5
        assert validator.results == []
    
    def test_generate_hard_instance(self):
        """Test hard instance generation."""
        validator = CompleteValidation()
        instance = validator.generate_hard_instance(10)
        
        assert 'graph' in instance
        assert 'formula' in instance
        assert 'n_vars' in instance
        assert 'n_clauses' in instance
        
        assert isinstance(instance['graph'], nx.Graph)
        # Check it's a CNFFormula-like object
        assert hasattr(instance['formula'], 'num_vars')
        assert hasattr(instance['formula'], 'clauses')
        assert instance['n_vars'] > 0
        assert instance['n_clauses'] > 0
    
    def test_treewidth_estimation_methods(self):
        """Test treewidth estimation methods."""
        validator = CompleteValidation()
        
        # Create a simple graph
        G = nx.path_graph(5)  # Path has treewidth 1
        tw = validator.estimate_treewidth(G)
        
        assert isinstance(tw, int)
        assert tw >= 1
        assert tw <= G.number_of_nodes()
    
    def test_min_degree_tw_upper_bound(self):
        """Test min-degree treewidth upper bound."""
        validator = CompleteValidation()
        
        # Path graph has treewidth 1
        G = nx.path_graph(5)
        tw = validator._min_degree_tw_upper_bound(G)
        
        assert tw >= 1
        assert tw <= 2  # Path should have low treewidth
    
    def test_spectral_tw_estimate(self):
        """Test spectral treewidth estimate."""
        validator = CompleteValidation()
        
        # Regular graph
        G = nx.cycle_graph(10)
        tw = validator._spectral_tw_estimate(G)
        
        assert isinstance(tw, int)
        assert tw >= 0
    
    def test_compute_information_complexity(self):
        """Test IC computation."""
        validator = CompleteValidation()
        
        # Create simple formula
        formula = CNFFormula(3, [[1, 2], [-1, 3], [2, -3]])
        ic = validator.compute_information_complexity(formula)
        
        assert isinstance(ic, float)
        assert ic >= 0
    
    def test_solve_with_dpll(self):
        """Test DPLL solving."""
        validator = CompleteValidation()
        
        # Create simple satisfiable formula
        formula = CNFFormula(2, [[1, 2], [-1, 2]])
        time_taken, solved = validator.solve_with_dpll(formula, timeout=10)
        
        assert isinstance(time_taken, float)
        assert isinstance(solved, bool)
        assert time_taken >= 0
        assert solved is True
    
    def test_validate_single_instance_small(self):
        """Test validation of single small instance."""
        validator = CompleteValidation()
        result = validator.validate_single_instance(10)
        
        assert 'n' in result
        assert 'n_vars' in result
        assert 'n_clauses' in result
        assert 'treewidth' in result
        assert 'information_complexity' in result
        assert 'time_dpll' in result
        assert 'solved_dpll' in result
        assert 'algorithms' in result
        
        assert result['n'] == 10
        assert result['treewidth'] > 0
        assert result['information_complexity'] > 0
    
    def test_run_complete_validation_mini(self):
        """Test complete validation run with minimal parameters."""
        validator = CompleteValidation(n_min=10, n_max=10, n_step=10)
        validator.run_complete_validation()
        
        assert len(validator.results) == 1
        assert validator.results[0]['n'] == 10
    
    def test_analyze_results(self):
        """Test results analysis."""
        validator = CompleteValidation(n_min=10, n_max=20, n_step=10)
        validator.run_complete_validation()
        
        # Should not raise exception
        validator.analyze_results()
        
        assert len(validator.results) == 2
    
    def test_save_results(self, tmp_path):
        """Test saving results to JSON."""
        validator = CompleteValidation(n_min=10, n_max=10, n_step=10)
        validator.run_complete_validation()
        
        output_file = tmp_path / "test_results.json"
        validator.save_results(output_file=str(output_file))
        
        assert output_file.exists()
        
        # Check file content
        import json
        with open(output_file) as f:
            data = json.load(f)
        
        assert 'parameters' in data
        assert 'results' in data
        assert len(data['results']) == 1
    
    def test_generate_plots(self, tmp_path):
        """Test plot generation."""
        validator = CompleteValidation(n_min=10, n_max=20, n_step=10)
        validator.run_complete_validation()
        
        output_dir = tmp_path / "plots"
        validator.generate_plots(output_dir=str(output_dir))
        
        plot_file = output_dir / "complete_validation.png"
        assert plot_file.exists()


class TestCorrelations:
    """Test correlation computations."""
    
    def test_correlations_positive(self):
        """Test that expected correlations are computed."""
        validator = CompleteValidation(n_min=10, n_max=30, n_step=10)
        validator.run_complete_validation()
        
        # Extract data
        tws = [r['treewidth'] for r in validator.results]
        ics = [r['information_complexity'] for r in validator.results]
        times = [r['time_dpll'] for r in validator.results]
        
        # Check that we have varying values
        assert len(set(tws)) > 1
        assert len(set(ics)) > 1
        
        # IC should correlate with treewidth
        from scipy.stats import pearsonr
        corr, _ = pearsonr(tws, ics)
        assert corr > 0.5  # Should be positive correlation


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
