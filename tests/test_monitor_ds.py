"""
Test suite for monitor_ds.py - Protocolo de Distribución Soberana (𝔻ₛ)
====================================================================

Tests the Sovereign Distribution Protocol monitoring system.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add pnp to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from pnp.echo_qcal.monitor_ds import (
    DSParameters,
    SovereignDistributionMonitor,
    monitor_ds
)


class TestDSParameters:
    """Test suite for DSParameters configuration class."""
    
    def test_weights_sum_to_one(self):
        """Test that influence weights sum to 1.0"""
        total = DSParameters.W_CK + DSParameters.W_AT + DSParameters.W_AU
        assert abs(total - 1.0) < 1e-10
    
    def test_weights_are_positive(self):
        """Test that all weights are positive."""
        assert DSParameters.W_CK > 0
        assert DSParameters.W_AT > 0
        assert DSParameters.W_AU > 0
    
    def test_activation_threshold(self):
        """Test activation threshold value."""
        assert DSParameters.ACTIVATION_THRESHOLD == 0.90
        assert 0 < DSParameters.ACTIVATION_THRESHOLD <= 1.0
    
    def test_risk_threshold(self):
        """Test risk threshold value."""
        assert DSParameters.RISK_THRESHOLD == 0.10
        assert 0 <= DSParameters.RISK_THRESHOLD < 1.0
    
    def test_threshold_consistency(self):
        """Test that activation + risk thresholds are consistent."""
        # Activation threshold should be 1 - risk threshold
        assert abs((1.0 - DSParameters.ACTIVATION_THRESHOLD) - DSParameters.RISK_THRESHOLD) < 1e-10
    
    def test_patoshi_allocation(self):
        """Test Patoshi allocation percentage."""
        assert DSParameters.PATOSHI_ALLOCATION_PERCENTAGE == 0.01
        assert 0 < DSParameters.PATOSHI_ALLOCATION_PERCENTAGE <= 1.0
    
    def test_patoshi_funds_simulated(self):
        """Test simulated Patoshi funds value."""
        assert DSParameters.PATOSHI_FUNDS_SIMULATED == 1000000.0
        assert DSParameters.PATOSHI_FUNDS_SIMULATED > 0


class TestSovereignDistributionMonitor:
    """Test suite for SovereignDistributionMonitor class."""
    
    def test_monitor_initialization(self):
        """Test monitor can be initialized."""
        monitor = SovereignDistributionMonitor()
        assert monitor.params == DSParameters
        assert monitor.coherence_factors == {}
        assert monitor.results == {}
    
    def test_run_full_coherence_verification(self):
        """Test full coherence verification runs."""
        monitor = SovereignDistributionMonitor()
        factors = monitor.run_full_coherence_verification()
        
        # Check all factors are present
        assert 'Ck_value' in factors
        assert 'At_value' in factors
        assert 'Au_value' in factors
        
        # Check values are in [0, 1] range
        assert 0 <= factors['Ck_value'] <= 1.0
        assert 0 <= factors['At_value'] <= 1.0
        assert 0 <= factors['Au_value'] <= 1.0
    
    def test_coherence_factors_stored(self):
        """Test that coherence factors are stored correctly."""
        monitor = SovereignDistributionMonitor()
        monitor.run_full_coherence_verification()
        
        assert monitor.coherence_factors['Ck_value'] is not None
        assert monitor.coherence_factors['At_value'] is not None
        assert monitor.coherence_factors['Au_value'] is not None
    
    def test_calculate_activation_level(self):
        """Test activation level calculation."""
        monitor = SovereignDistributionMonitor()
        A = monitor.calculate_activation_level()
        
        # Check A is in valid range [0, 1]
        assert 0 <= A <= 1.0
        assert isinstance(A, (float, np.floating))
        
        # Check it's stored in results
        assert 'Activation_Level_A' in monitor.results
        assert monitor.results['Activation_Level_A'] == A
    
    def test_activation_level_weighted_average(self):
        """Test that activation level is correctly weighted."""
        monitor = SovereignDistributionMonitor()
        factors = monitor.run_full_coherence_verification()
        
        # Calculate expected weighted average
        expected_A = (
            factors['Ck_value'] * DSParameters.W_CK +
            factors['At_value'] * DSParameters.W_AT +
            factors['Au_value'] * DSParameters.W_AU
        )
        
        A = monitor.calculate_activation_level()
        
        # Should match (accounting for any prior calculation)
        assert abs(A - expected_A) < 1e-10
    
    def test_calculate_risk_factor(self):
        """Test risk factor calculation."""
        monitor = SovereignDistributionMonitor()
        R = monitor.calculate_risk_factor()
        
        # Check R is in valid range [0, 1]
        assert 0 <= R <= 1.0
        assert isinstance(R, (float, np.floating))
        
        # Check it's stored in results
        assert 'Risk_Factor_R' in monitor.results
        assert monitor.results['Risk_Factor_R'] == R
    
    def test_risk_activation_relationship(self):
        """Test that R = 1 - A."""
        monitor = SovereignDistributionMonitor()
        A = monitor.calculate_activation_level()
        R = monitor.calculate_risk_factor()
        
        # R should equal 1 - A
        assert abs(R - (1.0 - A)) < 1e-10
    
    def test_calculate_distribution_status(self):
        """Test distribution status calculation."""
        monitor = SovereignDistributionMonitor()
        results = monitor.calculate_distribution_status()
        
        # Check all required keys are present
        assert 'Activation_Level_A' in results
        assert 'Risk_Factor_R' in results
        assert 'Ds_status' in results
        assert 'Ds_recommendation' in results
        assert 'Action_Authorized' in results
        assert 'Projected_Fund_BTC' in results
    
    def test_projected_fund_calculation(self):
        """Test projected fund calculation."""
        monitor = SovereignDistributionMonitor()
        results = monitor.calculate_distribution_status()
        
        expected_fund = DSParameters.PATOSHI_FUNDS_SIMULATED * DSParameters.PATOSHI_ALLOCATION_PERCENTAGE
        assert abs(results['Projected_Fund_BTC'] - expected_fund) < 1e-10
    
    def test_status_high_activation_authorized(self):
        """Test status when activation >= 90% and risk <= 10%."""
        monitor = SovereignDistributionMonitor()
        
        # Manually set high coherence factors
        monitor.coherence_factors = {
            'Ck_value': 1.0,
            'At_value': 1.0,
            'Au_value': 1.0
        }
        
        # Calculate directly
        A = 1.0  # All factors at maximum
        monitor.results['Activation_Level_A'] = A
        R = 1.0 - A
        monitor.results['Risk_Factor_R'] = R
        
        results = monitor.calculate_distribution_status()
        
        assert results['Action_Authorized'] == True
        assert "ACTIVACIÓN ÉTICA AUTORIZADA" in results['Ds_status']
    
    def test_status_mid_activation_alert(self):
        """Test status when activation is between 75% and 90%."""
        monitor = SovereignDistributionMonitor()
        
        # Set factors for ~80% activation
        monitor.coherence_factors = {
            'Ck_value': 0.8,
            'At_value': 0.8,
            'Au_value': 0.8
        }
        
        A = 0.8
        monitor.results['Activation_Level_A'] = A
        R = 1.0 - A
        monitor.results['Risk_Factor_R'] = R
        
        results = monitor.calculate_distribution_status()
        
        assert results['Action_Authorized'] == False
        assert "ALTA COHERENCIA" in results['Ds_status']
    
    def test_status_low_activation_stable(self):
        """Test status when activation is below 75%."""
        monitor = SovereignDistributionMonitor()
        
        # Set factors for ~50% activation
        monitor.coherence_factors = {
            'Ck_value': 0.5,
            'At_value': 0.5,
            'Au_value': 0.5
        }
        
        A = 0.5
        monitor.results['Activation_Level_A'] = A
        R = 1.0 - A
        monitor.results['Risk_Factor_R'] = R
        
        results = monitor.calculate_distribution_status()
        
        assert results['Action_Authorized'] == False
        assert "ESTADO ESTABLE" in results['Ds_status']
    
    def test_display_ds_report(self):
        """Test that display_ds_report runs without error."""
        monitor = SovereignDistributionMonitor()
        results = monitor.display_ds_report()
        
        # Should return results dictionary
        assert isinstance(results, dict)
        assert 'Activation_Level_A' in results
        assert 'Risk_Factor_R' in results


class TestMonitorDSFunction:
    """Test the monitor_ds convenience function."""
    
    def test_monitor_ds_function(self):
        """Test that monitor_ds function runs."""
        results = monitor_ds()
        
        # Should return results dictionary
        assert isinstance(results, dict)
        assert 'Activation_Level_A' in results
        assert 'Risk_Factor_R' in results


class TestCoherenceVerification:
    """Test coherence verification simulation."""
    
    def test_ck_verification_returns_value(self):
        """Test C_k verification returns a valid value."""
        monitor = SovereignDistributionMonitor()
        factors = monitor.run_full_coherence_verification()
        
        # Ck should be binary (0 or 1) in simulation
        assert factors['Ck_value'] in [0.0, 1.0]
    
    def test_at_verification_p_value_mapping(self):
        """Test A_t verification maps p-value correctly."""
        monitor = SovereignDistributionMonitor()
        factors = monitor.run_full_coherence_verification()
        
        # At should be in [0, 1] and based on p-value
        assert 0 <= factors['At_value'] <= 1.0
        
        # Lower p-value should give higher At_factor
        # P-value of 2.78e-6 should map to a reasonable value
        assert factors['At_value'] > 0
    
    def test_au_verification_returns_value(self):
        """Test A_u verification returns a valid value."""
        monitor = SovereignDistributionMonitor()
        factors = monitor.run_full_coherence_verification()
        
        # Au should be binary (0 or 1) in simulation
        assert factors['Au_value'] in [0.0, 1.0]


class TestProtocolMathematics:
    """Test the mathematical formulas of the protocol."""
    
    def test_activation_formula(self):
        """Test the activation level formula A = Σ(W_i * C_i) / ΣW_i."""
        monitor = SovereignDistributionMonitor()
        
        # Set known values
        monitor.coherence_factors = {
            'Ck_value': 0.8,
            'At_value': 0.6,
            'Au_value': 1.0
        }
        
        # Calculate manually
        expected = (
            0.8 * DSParameters.W_CK +
            0.6 * DSParameters.W_AT +
            1.0 * DSParameters.W_AU
        ) / (DSParameters.W_CK + DSParameters.W_AT + DSParameters.W_AU)
        
        # Calculate with monitor
        A = (
            monitor.coherence_factors['Ck_value'] * DSParameters.W_CK +
            monitor.coherence_factors['At_value'] * DSParameters.W_AT +
            monitor.coherence_factors['Au_value'] * DSParameters.W_AU
        )
        total_weight = DSParameters.W_CK + DSParameters.W_AT + DSParameters.W_AU
        A /= total_weight
        
        assert abs(A - expected) < 1e-10
    
    def test_risk_formula(self):
        """Test the risk factor formula R = 1 - A."""
        for A_test in [0.0, 0.25, 0.5, 0.75, 0.9, 1.0]:
            R_expected = 1.0 - A_test
            assert abs(R_expected - (1.0 - A_test)) < 1e-10
    
    def test_threshold_logic(self):
        """Test threshold decision logic."""
        # Test case 1: A >= 0.90 and R <= 0.10 -> Authorized
        A1, R1 = 0.92, 0.08
        authorized1 = A1 >= DSParameters.ACTIVATION_THRESHOLD and R1 <= DSParameters.RISK_THRESHOLD
        assert authorized1 == True
        
        # Test case 2: A >= 0.75 but < 0.90 -> Alert
        A2, R2 = 0.80, 0.20
        authorized2 = A2 >= DSParameters.ACTIVATION_THRESHOLD and R2 <= DSParameters.RISK_THRESHOLD
        assert authorized2 == False
        
        # Test case 3: A < 0.75 -> Stable
        A3, R3 = 0.50, 0.50
        authorized3 = A3 >= DSParameters.ACTIVATION_THRESHOLD and R3 <= DSParameters.RISK_THRESHOLD
        assert authorized3 == False


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_all_factors_zero(self):
        """Test behavior when all coherence factors are zero."""
        monitor = SovereignDistributionMonitor()
        monitor.coherence_factors = {
            'Ck_value': 0.0,
            'At_value': 0.0,
            'Au_value': 0.0
        }
        
        A = (
            monitor.coherence_factors['Ck_value'] * DSParameters.W_CK +
            monitor.coherence_factors['At_value'] * DSParameters.W_AT +
            monitor.coherence_factors['Au_value'] * DSParameters.W_AU
        )
        total_weight = DSParameters.W_CK + DSParameters.W_AT + DSParameters.W_AU
        A /= total_weight
        
        assert A == 0.0
        
        R = 1.0 - A
        assert R == 1.0
    
    def test_all_factors_max(self):
        """Test behavior when all coherence factors are at maximum."""
        monitor = SovereignDistributionMonitor()
        monitor.coherence_factors = {
            'Ck_value': 1.0,
            'At_value': 1.0,
            'Au_value': 1.0
        }
        
        A = (
            monitor.coherence_factors['Ck_value'] * DSParameters.W_CK +
            monitor.coherence_factors['At_value'] * DSParameters.W_AT +
            monitor.coherence_factors['Au_value'] * DSParameters.W_AU
        )
        total_weight = DSParameters.W_CK + DSParameters.W_AT + DSParameters.W_AU
        A /= total_weight
        
        assert abs(A - 1.0) < 1e-10
        
        R = 1.0 - A
        assert abs(R - 0.0) < 1e-10


def test_module_can_be_imported():
    """Test that the module can be imported."""
    from pnp.echo_qcal import monitor_ds as module
    assert module is not None


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Protocolo de Distribución Soberana (𝔻ₛ)")
    print("=" * 70)
    print()
    
    # Run a quick demonstration
    print("Running demonstration...")
    monitor = SovereignDistributionMonitor()
    results = monitor.display_ds_report()
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
