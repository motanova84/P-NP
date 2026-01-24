"""
Tests for QCAL ∞³ Validation Agents System

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
License: MIT
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

import pytest
import numpy as np
from qcal_validation_agents import (
    CoherenceMonitor,
    AccelerationValidator,
    TransitionTracker,
    QCALValidationSystem,
    COHERENCE_THRESHOLD,
    GRACIA_ACCELERATION
)
from qcal_infinity_cubed import (
    QCALInfinityCubed,
    PvsNPOperator,
    create_complete_qcal_system
)


class TestCoherenceMonitor:
    """Tests for CoherenceMonitor agent."""
    
    def test_initialization(self):
        """Test monitor initializes correctly."""
        monitor = CoherenceMonitor()
        assert monitor.name == "Coherence Monitor"
        assert monitor.threshold == COHERENCE_THRESHOLD
        assert len(monitor.history) == 0
    
    def test_measure_coherence(self):
        """Test coherence measurement."""
        monitor = CoherenceMonitor()
        qcal = create_complete_qcal_system()
        
        measurement = monitor.measure_coherence(qcal)
        
        assert 'coherence' in measurement
        assert 'state' in measurement
        assert 'status' in measurement
        assert 'transition_achieved' in measurement
        assert 0 <= measurement['coherence'] <= 2.0
    
    def test_coherence_states(self):
        """Test different coherence states are detected."""
        monitor = CoherenceMonitor()
        qcal = QCALInfinityCubed()
        qcal.register_operator(PvsNPOperator(num_vars=10, treewidth=5))
        
        measurement = monitor.measure_coherence(qcal)
        
        # Should be in one of the valid states
        assert measurement['state'] in ['INITIAL', 'BUILDING', 'APPROACHING', 'GRACIA']
    
    def test_prediction_insufficient_data(self):
        """Test prediction returns None with insufficient data."""
        monitor = CoherenceMonitor()
        prediction = monitor.predict_transition()
        assert prediction is None
    
    def test_status_report(self):
        """Test status report generation."""
        monitor = CoherenceMonitor()
        qcal = create_complete_qcal_system()
        
        monitor.measure_coherence(qcal)
        report = monitor.get_status_report()
        
        assert isinstance(report, str)
        assert 'COHERENCE MONITORING AGENT' in report


class TestAccelerationValidator:
    """Tests for AccelerationValidator agent."""
    
    def test_initialization(self):
        """Test validator initializes correctly."""
        validator = AccelerationValidator()
        assert validator.name == "Acceleration Validator"
        assert len(validator.benchmarks) == 0
    
    def test_benchmark_problem(self):
        """Test problem benchmarking."""
        validator = AccelerationValidator()
        
        result = validator.benchmark_problem(
            problem_size=50,
            treewidth=25,
            coherence=0.7
        )
        
        assert 'acceleration' in result
        assert 'classical_ic' in result
        assert 'qcal_ic' in result
        assert 'complexity_reduction' in result
        assert result['acceleration'] > 0
    
    def test_benchmark_with_high_coherence(self):
        """Test benchmarking with high coherence shows acceleration."""
        validator = AccelerationValidator()
        
        result = validator.benchmark_problem(
            problem_size=100,
            treewidth=50,
            coherence=0.9
        )
        
        # High coherence should reduce complexity
        assert result['complexity_reduction'] > 0
    
    def test_validate_hypothesis_insufficient_data(self):
        """Test validation with insufficient data."""
        validator = AccelerationValidator()
        
        validation = validator.validate_acceleration_hypothesis()
        
        assert not validation['valid']
        assert 'Insufficient' in validation['reason']
    
    def test_validate_hypothesis_with_data(self):
        """Test validation with sufficient benchmarks."""
        validator = AccelerationValidator()
        
        # Add multiple benchmarks with varying coherence
        for coherence in [0.5, 0.6, 0.7, 0.8]:
            validator.benchmark_problem(100, 50, coherence)
        
        validation = validator.validate_acceleration_hypothesis()
        
        assert 'valid' in validation
        assert 'correlation_acceleration' in validation
        assert 'interpretation' in validation
    
    def test_status_report(self):
        """Test status report generation."""
        validator = AccelerationValidator()
        validator.benchmark_problem(50, 25, 0.7)
        
        report = validator.get_status_report()
        
        assert isinstance(report, str)
        assert 'ACCELERATION VALIDATOR' in report


class TestTransitionTracker:
    """Tests for TransitionTracker agent."""
    
    def test_initialization(self):
        """Test tracker initializes correctly."""
        tracker = TransitionTracker()
        assert tracker.name == "NP→P Transition Tracker"
        assert not tracker.bifurcation_detected
        assert len(tracker.transitions) == 0
    
    def test_track_transition_np(self):
        """Test tracking in NP regime."""
        tracker = TransitionTracker()
        
        result = tracker.track_transition(
            coherence=0.5,
            problem_classification="NP-complete (Intractable)",
            info_complexity=100.0
        )
        
        assert not result['in_p_regime']
        assert result['coherence'] == 0.5
    
    def test_track_transition_p(self):
        """Test tracking in P regime."""
        tracker = TransitionTracker()
        
        result = tracker.track_transition(
            coherence=0.95,
            problem_classification="P (Tractable)",
            info_complexity=10.0
        )
        
        assert result['in_p_regime']
        assert result['coherence'] == 0.95
    
    def test_bifurcation_detection(self):
        """Test bifurcation point detection."""
        tracker = TransitionTracker()
        
        # Track progression from NP to P
        tracker.track_transition(0.7, "NP-complete (Intractable)", 100.0)
        tracker.track_transition(0.85, "NP-complete (Intractable)", 50.0)
        tracker.track_transition(0.92, "P (Tractable)", 10.0)
        
        assert tracker.bifurcation_detected
        assert tracker.bifurcation_coherence is not None
    
    def test_get_transition_curve_insufficient_data(self):
        """Test curve generation with insufficient data."""
        tracker = TransitionTracker()
        
        curve = tracker.get_transition_curve()
        assert curve is None
    
    def test_get_transition_curve_with_data(self):
        """Test curve generation with sufficient data."""
        tracker = TransitionTracker()
        
        # Add multiple tracking points
        for i in range(10):
            coherence = 0.5 + i * 0.05
            classification = "P (Tractable)" if coherence > 0.88 else "NP-complete (Intractable)"
            tracker.track_transition(coherence, classification, 100.0 / (i + 1))
        
        curve = tracker.get_transition_curve()
        
        assert curve is not None
        assert 'coherence_range' in curve
        assert 'complexity_range' in curve
        assert 'data_points' in curve
    
    def test_status_report(self):
        """Test status report generation."""
        tracker = TransitionTracker()
        tracker.track_transition(0.7, "NP-complete (Intractable)", 100.0)
        
        report = tracker.get_status_report()
        
        assert isinstance(report, str)
        assert 'TRANSITION TRACKER' in report


class TestQCALValidationSystem:
    """Tests for integrated QCALValidationSystem."""
    
    def test_initialization(self):
        """Test system initializes with all agents."""
        system = QCALValidationSystem()
        
        assert isinstance(system.coherence_monitor, CoherenceMonitor)
        assert isinstance(system.acceleration_validator, AccelerationValidator)
        assert isinstance(system.transition_tracker, TransitionTracker)
        assert len(system.validation_runs) == 0
    
    def test_run_validation(self):
        """Test running complete validation."""
        system = QCALValidationSystem()
        qcal = create_complete_qcal_system()
        
        result = system.run_validation(qcal)
        
        assert 'coherence' in result
        assert 'benchmark' in result
        assert 'transition' in result
        assert 'system_status' in result
        assert len(system.validation_runs) == 1
    
    def test_multiple_validations(self):
        """Test running multiple validations."""
        system = QCALValidationSystem()
        qcal = create_complete_qcal_system()
        
        # Run 3 validations
        for _ in range(3):
            system.run_validation(qcal)
        
        assert len(system.validation_runs) == 3
    
    def test_generate_full_report(self):
        """Test full report generation."""
        system = QCALValidationSystem()
        qcal = create_complete_qcal_system()
        
        system.run_validation(qcal)
        report = system.generate_full_report()
        
        assert isinstance(report, str)
        assert 'QCAL ∞³ HYPOTHESIS VALIDATION SYSTEM' in report
        assert 'EXECUTIVE SUMMARY' in report
    
    def test_save_validation_data(self, tmp_path):
        """Test saving validation data to file."""
        system = QCALValidationSystem()
        qcal = create_complete_qcal_system()
        
        system.run_validation(qcal)
        
        # Save to temp file
        filepath = tmp_path / "test_validation.json"
        system.save_validation_data(str(filepath))
        
        assert filepath.exists()
        
        # Load and verify
        import json
        with open(filepath, 'r') as f:
            data = json.load(f)
        
        assert 'system' in data
        assert 'total_runs' in data
        assert 'runs' in data
        assert 'constants' in data
        assert data['total_runs'] == 1


class TestConstants:
    """Test validation system constants."""
    
    def test_coherence_threshold(self):
        """Test coherence threshold is reasonable."""
        assert 0 < COHERENCE_THRESHOLD < 1
        assert abs(COHERENCE_THRESHOLD - 0.888) < 0.01
    
    def test_gracia_acceleration(self):
        """Test GRACIA acceleration is positive."""
        assert GRACIA_ACCELERATION > 1
        assert GRACIA_ACCELERATION > 1000  # Should be significant


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
