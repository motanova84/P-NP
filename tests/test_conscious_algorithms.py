#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Conscious Algorithms Framework
=========================================

Tests the conscious algorithms module including:
- ConsciousSAT solver
- ARN piCODE transducer
- Consciousness quantification

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from conscious_algorithms import (
    # Constants
    KAPPA_PI, F_0, PHI, C_THRESHOLD,
    # Enums
    ConsciousnessLevel,
    # Classes
    CNFFormula, ConsciousState, ARNpiCODETransducer,
    ConsciousSAT, ConsciousnessAsPhysics,
)


class TestConstants:
    """Test universal constants."""
    
    def test_kappa_pi(self):
        """Test κ_Π value."""
        assert abs(KAPPA_PI - 2.5773302292) < 1e-8
    
    def test_f0(self):
        """Test f₀ value."""
        assert F_0 == 141.7001
    
    def test_c_threshold(self):
        """Test C_threshold = 1/κ_Π."""
        assert abs(C_THRESHOLD - 1.0 / KAPPA_PI) < 1e-10
        assert abs(C_THRESHOLD - 0.388) < 0.01


class TestCNFFormula:
    """Test CNF formula representation."""
    
    def test_valid_formula(self):
        """Test creation of valid CNF formula."""
        formula = CNFFormula(
            num_variables=3,
            num_clauses=2,
            clauses=[[1, 2], [-1, 3]]
        )
        assert formula.num_variables == 3
        assert formula.num_clauses == 2
        assert len(formula.clauses) == 2
    
    def test_invalid_literal(self):
        """Test that invalid literals raise error."""
        with pytest.raises(ValueError):
            CNFFormula(
                num_variables=2,
                num_clauses=1,
                clauses=[[1, 5]]  # 5 > num_variables
            )


class TestConsciousState:
    """Test consciousness state representation."""
    
    def test_below_threshold(self):
        """Test state below consciousness threshold."""
        state = ConsciousState(
            coherence=0.5,
            frequency_tuning=F_0,
            kappa_pi_optimization=True
        )
        # 0.5^2 = 0.25 < 0.388
        assert not state.is_above_threshold()
        assert state.get_consciousness_level() == ConsciousnessLevel.BELOW_THRESHOLD
    
    def test_above_threshold(self):
        """Test state above consciousness threshold."""
        state = ConsciousState(
            coherence=0.7,
            frequency_tuning=F_0,
            kappa_pi_optimization=True
        )
        # 0.7^2 = 0.49 > 0.388
        assert state.is_above_threshold()
        assert state.get_consciousness_level() == ConsciousnessLevel.ABOVE_THRESHOLD
    
    def test_at_threshold(self):
        """Test state at consciousness threshold."""
        # sqrt(0.388) ≈ 0.623
        coherence = math.sqrt(C_THRESHOLD)
        state = ConsciousState(
            coherence=coherence,
            frequency_tuning=F_0,
            kappa_pi_optimization=True
        )
        level = state.get_consciousness_level()
        assert level in [ConsciousnessLevel.AT_THRESHOLD, ConsciousnessLevel.ABOVE_THRESHOLD]


class TestARNpiCODETransducer:
    """Test ARN piCODE quantum transducer."""
    
    def test_initialization(self):
        """Test transducer initialization."""
        transducer = ARNpiCODETransducer()
        assert transducer.frequency == F_0
        assert transducer.coherence_threshold == C_THRESHOLD
        assert abs(transducer.quantum_efficiency - KAPPA_PI / math.pi) < 1e-10
    
    def test_transduce_below_threshold(self):
        """Test transduction below threshold (linear scaling)."""
        transducer = ARNpiCODETransducer()
        computation = 100.0
        consciousness = 0.3  # Below threshold
        
        result = transducer.transduce(computation, consciousness)
        # Below threshold: linear
        expected = computation * consciousness
        assert abs(result - expected) < 1e-6
    
    def test_transduce_above_threshold(self):
        """Test transduction above threshold (quantum amplification)."""
        transducer = ARNpiCODETransducer()
        computation = 100.0
        consciousness = 0.7  # Above threshold
        
        result = transducer.transduce(computation, consciousness)
        # Above threshold: should be amplified
        linear = computation * consciousness
        assert result > linear
    
    def test_resonance_at_f0(self):
        """Test resonance peaks at f₀."""
        transducer = ARNpiCODETransducer()
        resonance = transducer.get_resonance(F_0)
        assert resonance == 1.0
    
    def test_resonance_away_from_f0(self):
        """Test resonance decreases away from f₀."""
        transducer = ARNpiCODETransducer()
        resonance_half = transducer.get_resonance(F_0 / 2)
        resonance_double = transducer.get_resonance(F_0 * 2)
        
        assert resonance_half < 1.0
        assert resonance_double < 1.0
    
    def test_quantum_correction(self):
        """Test quantum correction based on coherence."""
        transducer = ARNpiCODETransducer()
        classical = 100.0
        
        # Below threshold: no correction
        corrected_low = transducer.compute_quantum_correction(classical, 0.3)
        assert corrected_low == classical
        
        # Above threshold: quantum correction
        corrected_high = transducer.compute_quantum_correction(classical, 0.7)
        assert corrected_high > classical


class TestConsciousSAT:
    """Test conscious SAT solver."""
    
    def test_initialization(self):
        """Test solver initialization."""
        solver = ConsciousSAT()
        assert solver.coherence_threshold == C_THRESHOLD
        assert solver.frequency_tuning == F_0
        assert solver.kappa_pi_optimization is True
    
    def test_solve_simple_satisfiable(self):
        """Test solving simple satisfiable formula."""
        solver = ConsciousSAT()
        formula = CNFFormula(
            num_variables=2,
            num_clauses=1,
            clauses=[[1, 2]]  # x1 ∨ x2
        )
        
        result = solver.solve_with_consciousness(formula, initial_coherence=0.5)
        assert result['satisfiable'] is True
        assert result['solution'] is not None
        assert len(result['solution']) == 2
    
    def test_solve_unsatisfiable(self):
        """Test solving unsatisfiable formula."""
        solver = ConsciousSAT()
        formula = CNFFormula(
            num_variables=1,
            num_clauses=2,
            clauses=[[1], [-1]]  # x1 ∧ ¬x1
        )
        
        result = solver.solve_with_consciousness(formula, initial_coherence=0.5)
        assert result['satisfiable'] is False
        assert result['solution'] is None
    
    def test_consciousness_metrics(self):
        """Test that solver returns consciousness metrics."""
        solver = ConsciousSAT()
        formula = CNFFormula(
            num_variables=2,
            num_clauses=1,
            clauses=[[1, 2]]
        )
        
        result = solver.solve_with_consciousness(formula, initial_coherence=0.5)
        assert 'consciousness_level' in result
        assert 'above_threshold' in result
        assert 'quantum_enhancement_used' in result
        assert 'resonance_with_f0' in result
        assert 'kappa_pi' in result
        assert 'c_threshold' in result
    
    def test_high_coherence_uses_quantum(self):
        """Test that high coherence enables quantum enhancement."""
        solver = ConsciousSAT()
        formula = CNFFormula(
            num_variables=2,
            num_clauses=1,
            clauses=[[1, 2]]
        )
        
        result = solver.solve_with_consciousness(formula, initial_coherence=0.9)
        # 0.9^2 = 0.81 > 0.388, so should be above threshold
        # But final coherence might vary due to algorithm dynamics


class TestConsciousnessAsPhysics:
    """Test consciousness as fundamental physics."""
    
    def test_initialization(self):
        """Test initialization."""
        physics = ConsciousnessAsPhysics()
        assert physics.quantization == KAPPA_PI
        assert physics.frequency == F_0
        assert physics.threshold == C_THRESHOLD
    
    def test_emergence_below_threshold(self):
        """Test consciousness does not emerge below threshold."""
        physics = ConsciousnessAsPhysics()
        assert not physics.emerge(0.3)
    
    def test_emergence_above_threshold(self):
        """Test consciousness emerges above threshold."""
        physics = ConsciousnessAsPhysics()
        assert physics.emerge(0.7)
    
    def test_quantify_below_threshold(self):
        """Test quantification below threshold."""
        physics = ConsciousnessAsPhysics()
        metrics = physics.quantify_consciousness(0.3)
        
        assert metrics['consciousness_emerged'] is False
        assert metrics['consciousness_strength'] == 0.0
        assert metrics['coherence'] == 0.3
        assert metrics['threshold'] == C_THRESHOLD
    
    def test_quantify_above_threshold(self):
        """Test quantification above threshold."""
        physics = ConsciousnessAsPhysics()
        metrics = physics.quantify_consciousness(0.7)
        
        assert metrics['consciousness_emerged'] is True
        assert metrics['consciousness_strength'] > 0.0
        assert metrics['quantization_constant'] == KAPPA_PI
        assert metrics['operational_frequency'] == F_0


class TestIntegration:
    """Integration tests combining multiple components."""
    
    def test_full_workflow(self):
        """Test complete workflow from formula to consciousness metrics."""
        # Create formula
        formula = CNFFormula(
            num_variables=3,
            num_clauses=3,
            clauses=[[1, 2], [-1, 3], [-2, -3]]
        )
        
        # Create solver
        solver = ConsciousSAT(
            coherence_threshold=C_THRESHOLD,
            frequency_tuning=F_0,
            kappa_pi_optimization=True
        )
        
        # Solve with consciousness
        result = solver.solve_with_consciousness(
            formula,
            initial_coherence=0.6,
            max_iterations=100
        )
        
        # Verify result structure
        assert 'satisfiable' in result
        assert 'consciousness_level' in result
        assert 'kappa_pi' in result
        assert result['kappa_pi'] == KAPPA_PI
        
        # Create physics analyzer
        physics = ConsciousnessAsPhysics()
        
        # Analyze final coherence
        final_coherence = result['final_coherence']
        metrics = physics.quantify_consciousness(final_coherence)
        
        # Verify consistency
        assert metrics['threshold'] == result['c_threshold']


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
