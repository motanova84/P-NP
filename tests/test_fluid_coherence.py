"""
Tests for Fluid Coherence System
=================================

Tests for the gravitational hierarchy harmonic system implementation.
"""

import pytest
import sys
import math
sys.path.insert(0, 'src')

from fluid_coherence import (
    F0_ROOT,
    KAPPA_COUPLING,
    COHERENCE_TURBULENT_THRESHOLD,
    COHERENCE_SUPERFLUID_THRESHOLD,
    NU_BASE,
    effective_viscosity,
    coherence_state,
    computational_complexity_state,
    harmonic_layer_frequency,
    dimensional_lamination_factor,
    vortex_singularity_metrics,
    information_flow_rate,
    complexity_collapse_factor,
    analyze_fluid_system,
    demonstrate_coherence_transition
)


class TestConstants:
    """Test that fundamental constants are correctly defined."""
    
    def test_root_frequency(self):
        """Test that root frequency is 141.7001 Hz."""
        assert abs(F0_ROOT - 141.7001) < 1e-4
    
    def test_coupling_constant(self):
        """Test that coupling constant is 1/7."""
        assert abs(KAPPA_COUPLING - 1.0/7.0) < 1e-6
        assert abs(KAPPA_COUPLING - 0.142857) < 1e-5
    
    def test_coherence_thresholds(self):
        """Test coherence threshold values."""
        assert COHERENCE_TURBULENT_THRESHOLD == 0.88
        assert COHERENCE_SUPERFLUID_THRESHOLD == 0.95
        assert COHERENCE_SUPERFLUID_THRESHOLD > COHERENCE_TURBULENT_THRESHOLD


class TestEffectiveViscosity:
    """Test effective viscosity calculations."""
    
    def test_viscosity_at_low_coherence(self):
        """Test viscosity is high at low coherence."""
        nu_low = effective_viscosity(0.1)
        nu_high = effective_viscosity(0.9)
        assert nu_low > nu_high
    
    def test_viscosity_at_perfect_coherence(self):
        """Test viscosity approaches minimum at Ψ → 1."""
        nu = effective_viscosity(1.0)
        expected = NU_BASE / KAPPA_COUPLING
        assert abs(nu - expected) < 1e-6
    
    def test_viscosity_invalid_coherence(self):
        """Test that invalid coherence raises error."""
        with pytest.raises(ValueError):
            effective_viscosity(0.0)
        with pytest.raises(ValueError):
            effective_viscosity(-0.5)
        with pytest.raises(ValueError):
            effective_viscosity(1.5)
    
    def test_viscosity_formula(self):
        """Test viscosity formula: ν_eff = ν_base / (κ · Ψ)."""
        psi = 0.7
        nu = effective_viscosity(psi)
        expected = NU_BASE / (KAPPA_COUPLING * psi)
        assert abs(nu - expected) < 1e-10


class TestCoherenceState:
    """Test coherence state classification."""
    
    def test_turbulent_state(self):
        """Test turbulent state detection."""
        assert coherence_state(0.5) == "turbulent"
        assert coherence_state(0.87) == "turbulent"
        assert coherence_state(0.1) == "turbulent"
    
    def test_transition_state(self):
        """Test transition state detection."""
        assert coherence_state(0.88) == "transition"
        assert coherence_state(0.90) == "transition"
        assert coherence_state(0.94) == "transition"
    
    def test_superfluid_state(self):
        """Test superfluid state detection."""
        assert coherence_state(0.95) == "superfluid"
        assert coherence_state(0.99) == "superfluid"
        assert coherence_state(1.0) == "superfluid"
    
    def test_boundary_conditions(self):
        """Test state boundaries."""
        # Just below turbulent threshold
        assert coherence_state(COHERENCE_TURBULENT_THRESHOLD - 0.01) == "turbulent"
        # At turbulent threshold
        assert coherence_state(COHERENCE_TURBULENT_THRESHOLD) == "transition"
        # Just below superfluid threshold
        assert coherence_state(COHERENCE_SUPERFLUID_THRESHOLD - 0.01) == "transition"
        # At superfluid threshold
        assert coherence_state(COHERENCE_SUPERFLUID_THRESHOLD) == "superfluid"


class TestComputationalComplexity:
    """Test computational complexity state mapping."""
    
    def test_turbulent_gives_p_neq_np(self):
        """Test that turbulent state gives P ≠ NP."""
        assert computational_complexity_state(0.5) == "P ≠ NP"
        assert computational_complexity_state(0.87) == "P ≠ NP"
    
    def test_superfluid_gives_p_eq_np(self):
        """Test that superfluid state gives P = NP."""
        assert computational_complexity_state(0.95) == "P = NP"
        assert computational_complexity_state(0.99) == "P = NP"
        assert computational_complexity_state(1.0) == "P = NP"
    
    def test_transition_state_complexity(self):
        """Test transition state complexity."""
        result = computational_complexity_state(0.90)
        assert "transition" in result.lower()


class TestHarmonicLayers:
    """Test harmonic layer frequency calculations."""
    
    def test_first_layer(self):
        """Test first harmonic layer."""
        f1 = harmonic_layer_frequency(1)
        assert abs(f1 - F0_ROOT) < 1e-4
    
    def test_second_layer(self):
        """Test second harmonic layer."""
        f2 = harmonic_layer_frequency(2)
        assert abs(f2 - 2 * F0_ROOT) < 1e-4
    
    def test_seventh_layer(self):
        """Test seventh harmonic layer (related to κ = 1/7)."""
        f7 = harmonic_layer_frequency(7)
        assert abs(f7 - 7 * F0_ROOT) < 1e-3
    
    def test_custom_root_frequency(self):
        """Test custom root frequency."""
        custom_f0 = 100.0
        f3 = harmonic_layer_frequency(3, f0=custom_f0)
        assert abs(f3 - 300.0) < 1e-6
    
    def test_invalid_layer(self):
        """Test that invalid layer raises error."""
        with pytest.raises(ValueError):
            harmonic_layer_frequency(0)
        with pytest.raises(ValueError):
            harmonic_layer_frequency(-1)


class TestDimensionalLamination:
    """Test dimensional lamination factor."""
    
    def test_turbulent_lamination(self):
        """Test lamination in turbulent state."""
        lam = dimensional_lamination_factor(0.5)
        assert lam < 1.0
        assert lam == pytest.approx(KAPPA_COUPLING * 0.5, rel=1e-6)
    
    def test_superfluid_lamination(self):
        """Test perfect lamination in superfluid state."""
        lam = dimensional_lamination_factor(0.99)
        assert lam == pytest.approx(1.0, rel=1e-2)
    
    def test_transition_lamination(self):
        """Test lamination increases through transition."""
        lam_low = dimensional_lamination_factor(0.88)
        lam_mid = dimensional_lamination_factor(0.92)
        lam_high = dimensional_lamination_factor(0.94)
        assert lam_low < lam_mid < lam_high
    
    def test_lamination_bounds(self):
        """Test lamination factor bounds."""
        for psi in [0.1, 0.5, 0.88, 0.92, 0.95, 0.99]:
            lam = dimensional_lamination_factor(psi)
            assert 0.0 <= lam <= 1.0


class TestVortexSingularity:
    """Test vortex singularity metrics."""
    
    def test_basic_metrics(self):
        """Test basic vortex metrics calculation."""
        metrics = vortex_singularity_metrics(0.1, 0.9)
        assert 'pressure' in metrics
        assert 'velocity' in metrics
        assert 'metric_grr' in metrics
        assert 'singularity_strength' in metrics
    
    def test_pressure_decreases_with_radius(self):
        """Test pressure falls as r → 0."""
        p1 = vortex_singularity_metrics(1.0, 0.9)['pressure']
        p2 = vortex_singularity_metrics(0.5, 0.9)['pressure']
        p3 = vortex_singularity_metrics(0.1, 0.9)['pressure']
        assert p1 > p2 > p3
    
    def test_velocity_diverges_as_radius_decreases(self):
        """Test velocity → ∞ as r → 0."""
        v1 = vortex_singularity_metrics(1.0, 0.9)['velocity']
        v2 = vortex_singularity_metrics(0.5, 0.9)['velocity']
        v3 = vortex_singularity_metrics(0.1, 0.9)['velocity']
        assert v1 < v2 < v3
    
    def test_metric_singularity(self):
        """Test metric component g_rr diverges."""
        g1 = vortex_singularity_metrics(1.0, 0.9)['metric_grr']
        g2 = vortex_singularity_metrics(0.1, 0.9)['metric_grr']
        assert g2 > g1
    
    def test_coherence_affects_singularity(self):
        """Test singularity strength increases with coherence."""
        s_low = vortex_singularity_metrics(0.1, 0.5)['singularity_strength']
        s_high = vortex_singularity_metrics(0.1, 0.95)['singularity_strength']
        assert s_high > s_low
    
    def test_invalid_radius(self):
        """Test that invalid radius raises error."""
        with pytest.raises(ValueError):
            vortex_singularity_metrics(0.0, 0.9)
        with pytest.raises(ValueError):
            vortex_singularity_metrics(-0.5, 0.9)


class TestInformationFlow:
    """Test information flow rate calculations."""
    
    def test_flow_increases_with_coherence(self):
        """Test flow rate increases with coherence."""
        flow_low = information_flow_rate(0.5, 50.0)
        flow_high = information_flow_rate(0.95, 50.0)
        assert flow_high > flow_low
    
    def test_flow_decreases_with_treewidth(self):
        """Test flow rate decreases with treewidth."""
        flow_low_tw = information_flow_rate(0.9, 10.0)
        flow_high_tw = information_flow_rate(0.9, 100.0)
        assert flow_low_tw > flow_high_tw
    
    def test_superfluid_amplification(self):
        """Test superfluid state amplifies flow."""
        flow_turbulent = information_flow_rate(0.7, 50.0)
        flow_superfluid = information_flow_rate(0.97, 50.0)
        # Superfluid should have significantly higher flow
        assert flow_superfluid > flow_turbulent * 10


class TestComplexityCollapse:
    """Test complexity collapse factor."""
    
    def test_no_collapse_in_turbulent(self):
        """Test no collapse in turbulent state."""
        collapse = complexity_collapse_factor(0.7)
        assert collapse == 0.0
    
    def test_near_complete_collapse_in_superfluid(self):
        """Test near-complete collapse in superfluid."""
        collapse = complexity_collapse_factor(0.99)
        assert collapse > 0.95
    
    def test_collapse_increases_monotonically(self):
        """Test collapse factor increases with coherence."""
        c1 = complexity_collapse_factor(0.88)
        c2 = complexity_collapse_factor(0.92)
        c3 = complexity_collapse_factor(0.95)
        c4 = complexity_collapse_factor(0.99)
        assert c1 < c2 < c3 < c4
    
    def test_collapse_bounds(self):
        """Test collapse factor is in [0, 1]."""
        for psi in [0.5, 0.88, 0.92, 0.95, 0.99]:
            collapse = complexity_collapse_factor(psi)
            assert 0.0 <= collapse <= 1.0


class TestAnalyzeFluidSystem:
    """Test comprehensive system analysis."""
    
    def test_analysis_structure(self):
        """Test that analysis returns all expected fields."""
        analysis = analyze_fluid_system(0.9)
        required_fields = [
            'coherence', 'state', 'complexity_relation',
            'effective_viscosity', 'lamination_factor',
            'information_flow_rate', 'complexity_collapse',
            'vortex_metrics', 'treewidth', 'radius',
            'frequency_root', 'coupling_constant'
        ]
        for field in required_fields:
            assert field in analysis
    
    def test_turbulent_analysis(self):
        """Test analysis of turbulent state."""
        analysis = analyze_fluid_system(0.7, treewidth=50.0)
        assert analysis['state'] == 'turbulent'
        assert 'P ≠ NP' in analysis['complexity_relation']
        assert analysis['complexity_collapse'] == 0.0
    
    def test_superfluid_analysis(self):
        """Test analysis of superfluid state."""
        analysis = analyze_fluid_system(0.97, treewidth=50.0)
        assert analysis['state'] == 'superfluid'
        assert 'P = NP' in analysis['complexity_relation']
        assert analysis['complexity_collapse'] > 0.95


class TestCoherenceTransition:
    """Test coherence transition demonstration."""
    
    def test_transition_steps(self):
        """Test transition produces expected number of steps."""
        results = demonstrate_coherence_transition(0.5, 1.0, steps=10)
        assert len(results) == 10
    
    def test_transition_progression(self):
        """Test coherence increases through transition."""
        results = demonstrate_coherence_transition(0.5, 1.0, steps=5)
        coherences = [r['coherence'] for r in results]
        # Check monotonic increase
        for i in range(len(coherences) - 1):
            assert coherences[i] < coherences[i + 1]
    
    def test_transition_shows_state_change(self):
        """Test transition captures state changes."""
        results = demonstrate_coherence_transition(0.8, 1.0, steps=20)
        states = [r['state'] for r in results]
        # Should see all three states
        assert 'turbulent' in states
        assert 'transition' in states
        assert 'superfluid' in states


class TestPhysicalProperties:
    """Test physical properties and relationships."""
    
    def test_viscosity_coherence_inverse_relationship(self):
        """Test viscosity inversely proportional to coherence."""
        # ν_eff = ν_base / (κ · Ψ)
        # So ν_eff · Ψ = ν_base / κ = constant
        for psi in [0.1, 0.5, 0.9, 0.99]:
            nu = effective_viscosity(psi)
            product = nu * psi
            expected = NU_BASE / KAPPA_COUPLING
            assert abs(product - expected) < 1e-6
    
    def test_dimensional_coupling_enables_lamination(self):
        """Test that κ = 1/7 enables proper lamination."""
        # At high coherence, lamination should approach 1
        # κ controls the rate of approach
        lam_95 = dimensional_lamination_factor(0.95)
        assert lam_95 == pytest.approx(1.0, rel=1e-2)
    
    def test_harmonic_structure(self):
        """Test harmonic structure of frequency layers."""
        # Frequencies should form harmonic series
        freqs = [harmonic_layer_frequency(i) for i in range(1, 8)]
        # Check they're multiples of f0
        for i, freq in enumerate(freqs, 1):
            assert abs(freq - i * F0_ROOT) < 1e-3


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
