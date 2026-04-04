"""
Tests for Global PSI Field (Campo de Coherencia Global Ψ)
==========================================================

Test suite for the noesis.global_psi_field module implementing
the Noetic Machine theorem: L ∈ NP ↔ L ∈ P_Noetic under critical coherence.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import math
import pytest
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from noesis.global_psi_field import (
    F0_FUNDAMENTAL,
    PHI,
    PHI_SQUARED,
    KAPPA_PI,
    PSI_CRITICAL_THRESHOLD,
    F0_ALIGNMENT_TOLERANCE,
    CoherenceState,
    Alignment,
    Language,
    NoeticMachine,
    noetic_collapse,
    collapse_via_quantum_noetic_resonance,
)


# ============================================================================
# CONSTANTS
# ============================================================================

class TestConstants:
    """Test fundamental constants of the PSI field."""

    def test_f0_fundamental(self):
        """f₀ = 141.7001 Hz."""
        assert F0_FUNDAMENTAL == 141.7001

    def test_phi(self):
        """φ = (1 + √5) / 2."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-14

    def test_phi_squared(self):
        """φ² = φ · φ."""
        assert abs(PHI_SQUARED - PHI ** 2) < 1e-14

    def test_kappa_pi(self):
        """κ_Π = 2.5773."""
        assert KAPPA_PI == 2.5773

    def test_psi_critical_threshold(self):
        """Critical coherence threshold = 0.9999998."""
        assert PSI_CRITICAL_THRESHOLD == 0.9999998

    def test_f0_alignment_tolerance(self):
        """Alignment tolerance = 1e-6."""
        assert F0_ALIGNMENT_TOLERANCE == 1e-6


# ============================================================================
# CoherenceState
# ============================================================================

class TestCoherenceState:
    """Tests for the CoherenceState class."""

    def test_valid_coherence(self):
        """CoherenceState accepts values in [0, 1]."""
        psi = CoherenceState(val=0.95)
        assert psi.val == 0.95

    def test_critical_coherence_above_threshold(self):
        """Coherence ≥ 0.9999998 is critical."""
        psi = CoherenceState(val=0.9999998)
        assert psi.is_critical is True

    def test_critical_coherence_exactly_threshold(self):
        """Coherence == 0.9999998 is critical."""
        psi = CoherenceState(val=PSI_CRITICAL_THRESHOLD)
        assert psi.is_critical is True

    def test_subcritical_coherence(self):
        """Coherence < 0.9999998 is not critical."""
        psi = CoherenceState(val=0.999)
        assert psi.is_critical is False

    def test_perfect_coherence(self):
        """val=1.0 is the maximum coherence state."""
        psi = CoherenceState(val=1.0)
        assert psi.is_critical is True
        assert psi.val == 1.0

    def test_zero_coherence(self):
        """val=0.0 is minimum coherence."""
        psi = CoherenceState(val=0.0)
        assert psi.is_critical is False

    def test_invalid_coherence_above_one(self):
        """val > 1 raises ValueError."""
        with pytest.raises(ValueError):
            CoherenceState(val=1.1)

    def test_invalid_coherence_negative(self):
        """val < 0 raises ValueError."""
        with pytest.raises(ValueError):
            CoherenceState(val=-0.1)

    def test_resonance_frequency(self):
        """Resonance frequency = f₀ · Ψ."""
        psi = CoherenceState(val=0.5)
        expected = F0_FUNDAMENTAL * 0.5
        assert abs(psi.resonance_frequency - expected) < 1e-10

    def test_resonance_frequency_at_perfect_coherence(self):
        """At Ψ=1, resonance frequency equals f₀."""
        psi = CoherenceState(val=1.0)
        assert abs(psi.resonance_frequency - F0_FUNDAMENTAL) < 1e-10

    def test_repr_contains_critical(self):
        """repr for critical state contains 'CRÍTICA'."""
        psi = CoherenceState(val=0.9999999)
        assert "CRÍTICA" in repr(psi)

    def test_repr_contains_subcritical(self):
        """repr for sub-critical state contains 'sub-crítica'."""
        psi = CoherenceState(val=0.5)
        assert "sub-crítica" in repr(psi)


# ============================================================================
# Alignment
# ============================================================================

class TestAlignment:
    """Tests for the Alignment class."""

    def test_exact_f0_alignment(self):
        """Frequency = f₀ gives perfect alignment."""
        a = Alignment(frequency=F0_FUNDAMENTAL)
        assert a.is_aligned is True
        assert a.deviation == 0.0

    def test_near_f0_alignment(self):
        """Frequency within tolerance is aligned."""
        tiny_offset = F0_FUNDAMENTAL * 1e-7  # well within 1e-6
        a = Alignment(frequency=F0_FUNDAMENTAL + tiny_offset)
        assert a.is_aligned is True

    def test_out_of_f0_alignment(self):
        """Frequency outside tolerance is not aligned."""
        large_offset = F0_FUNDAMENTAL * 1e-3  # >> 1e-6
        a = Alignment(frequency=F0_FUNDAMENTAL + large_offset)
        assert a.is_aligned is False

    def test_resonance_factor_at_perfect_alignment(self):
        """Resonance factor ρ = 1 when frequency = f₀."""
        a = Alignment(frequency=F0_FUNDAMENTAL)
        assert abs(a.resonance_factor - 1.0) < 1e-14

    def test_resonance_factor_decreases_with_deviation(self):
        """Resonance factor decreases as frequency deviates from f₀."""
        a_close = Alignment(frequency=F0_FUNDAMENTAL + 0.001)
        a_far = Alignment(frequency=F0_FUNDAMENTAL + 1.0)
        assert a_close.resonance_factor > a_far.resonance_factor

    def test_deviation_calculation(self):
        """Deviation = |f - f₀| / f₀."""
        a = Alignment(frequency=F0_FUNDAMENTAL + F0_FUNDAMENTAL * 0.01)
        assert abs(a.deviation - 0.01) < 1e-14

    def test_repr_contains_aligned(self):
        """repr for aligned state contains 'ALINEADO'."""
        a = Alignment(frequency=F0_FUNDAMENTAL)
        assert "ALINEADO" in repr(a)

    def test_repr_contains_desalineado(self):
        """repr for misaligned state contains 'desalineado'."""
        a = Alignment(frequency=1.0)
        assert "desalineado" in repr(a)


# ============================================================================
# Language
# ============================================================================

class TestLanguage:
    """Tests for the Language class."""

    def test_language_creation(self):
        """Language can be created with name and decision function."""
        lang = Language(name="SAT", decision=lambda x: True)
        assert lang.name == "SAT"
        assert lang.is_in_NP is True

    def test_language_decide(self):
        """Language.decide invokes the oracle."""
        lang = Language(name="TRIVIAL", decision=lambda x: len(x) > 0)
        assert lang.decide("hello") is True
        assert lang.decide("") is False

    def test_language_without_decision_raises(self):
        """Language.decide raises NotImplementedError if no decision function."""
        lang = Language(name="ABSTRACT")
        with pytest.raises(NotImplementedError):
            lang.decide("x")

    def test_language_not_in_np(self):
        """Language can be marked as outside NP."""
        lang = Language(name="UNDECIDABLE", is_in_NP=False)
        assert lang.is_in_NP is False

    def test_repr(self):
        """repr contains name and complexity class."""
        lang = Language(name="3SAT")
        assert "3SAT" in repr(lang)
        assert "NP" in repr(lang)


# ============================================================================
# NoeticMachine
# ============================================================================

class TestNoeticMachine:
    """Tests for the NoeticMachine class."""

    def _make_critical_machine(self) -> NoeticMachine:
        """Helper: create a NoeticMachine with critical coherence."""
        psi = CoherenceState(val=0.9999999)
        align = Alignment(frequency=F0_FUNDAMENTAL)
        return NoeticMachine(coherence=psi, f0_alignment=align)

    def test_machine_creation(self):
        """NoeticMachine is created under critical coherence and alignment."""
        machine = self._make_critical_machine()
        assert machine.coherence.is_critical is True
        assert machine.f0_alignment.is_aligned is True

    def test_machine_rejects_subcritical_coherence(self):
        """NoeticMachine raises ValueError with sub-critical coherence."""
        psi = CoherenceState(val=0.5)
        align = Alignment(frequency=F0_FUNDAMENTAL)
        with pytest.raises(ValueError, match="Coherencia insuficiente"):
            NoeticMachine(coherence=psi, f0_alignment=align)

    def test_machine_rejects_misaligned_frequency(self):
        """NoeticMachine raises ValueError with misaligned frequency."""
        psi = CoherenceState(val=0.9999999)
        align = Alignment(frequency=1.0)  # far from f₀
        with pytest.raises(ValueError):
            NoeticMachine(coherence=psi, f0_alignment=align)

    def test_effective_complexity_exponent(self):
        """Effective complexity exponent is close to κ_Π under critical coherence."""
        machine = self._make_critical_machine()
        kappa_eff = machine.effective_complexity_exponent
        # Under Ψ≈1 and ρ≈1, κ_eff ≈ κ_Π
        assert abs(kappa_eff - KAPPA_PI) < 0.01

    def test_solve_np_language(self):
        """NoeticMachine.solve resolves NP language instances correctly."""
        machine = self._make_critical_machine()
        lang = Language(name="3SAT", decision=lambda x: len(x) % 2 == 0)
        assert machine.solve(lang, "ab") is True
        assert machine.solve(lang, "abc") is False

    def test_solve_non_np_language_raises(self):
        """NoeticMachine.solve raises ValueError for non-NP languages."""
        machine = self._make_critical_machine()
        lang = Language(name="HALT", decision=lambda x: False, is_in_NP=False)
        with pytest.raises(ValueError):
            machine.solve(lang, "x")

    def test_repr(self):
        """repr contains coherence and alignment info."""
        machine = self._make_critical_machine()
        r = repr(machine)
        assert "NoeticMachine" in r
        assert "CoherenceState" in r


# ============================================================================
# noetic_collapse / collapse_via_quantum_noetic_resonance
# ============================================================================

class TestNoeticCollapse:
    """Tests for the noetic_collapse function (L ∈ NP ↔ L ∈ P_Noetic)."""

    def _make_machine(self) -> NoeticMachine:
        psi = CoherenceState(val=0.9999999)
        align = Alignment(frequency=F0_FUNDAMENTAL)
        return NoeticMachine(coherence=psi, f0_alignment=align)

    def test_collapse_true_for_np_language(self):
        """noetic_collapse returns True for L ∈ NP under critical coherence."""
        machine = self._make_machine()
        lang = Language(name="SAT", is_in_NP=True, decision=lambda x: True)
        assert noetic_collapse(machine, lang) is True

    def test_collapse_false_for_non_np_language(self):
        """noetic_collapse returns False for L ∉ NP (no equivalence)."""
        machine = self._make_machine()
        lang = Language(name="HALT", is_in_NP=False, decision=lambda x: False)
        assert noetic_collapse(machine, lang) is False

    def test_oracle_result_structure(self):
        """collapse_via_quantum_noetic_resonance returns expected dict keys."""
        machine = self._make_machine()
        lang = Language(name="3-COLOR", is_in_NP=True, decision=lambda x: True)
        result = collapse_via_quantum_noetic_resonance(machine, lang)

        assert "colapso_activo" in result
        assert "psi" in result
        assert "rho_resonancia" in result
        assert "kappa_efectivo" in result
        assert "lenguaje" in result
        assert "en_NP" in result
        assert "en_P_Noetic" in result
        assert "equivalencia" in result
        assert "mecanismo" in result
        assert "frecuencia_efectiva" in result
        assert "sello" in result

    def test_oracle_collapse_active(self):
        """Oracle shows collapse active for critical coherence and f₀ alignment."""
        machine = self._make_machine()
        lang = Language(name="SAT", is_in_NP=True, decision=lambda x: True)
        result = collapse_via_quantum_noetic_resonance(machine, lang)
        assert result["colapso_activo"] is True
        assert result["en_NP"] is True
        assert result["en_P_Noetic"] is True
        assert result["equivalencia"] is True

    def test_oracle_psi_value(self):
        """Oracle result contains the correct Ψ value."""
        machine = self._make_machine()
        lang = Language(name="SAT", is_in_NP=True, decision=lambda x: True)
        result = collapse_via_quantum_noetic_resonance(machine, lang)
        assert abs(result["psi"] - 0.9999999) < 1e-10

    def test_oracle_resonance_near_one(self):
        """Under perfect f₀ alignment, resonance factor ρ ≈ 1."""
        machine = self._make_machine()
        lang = Language(name="SAT", is_in_NP=True, decision=lambda x: True)
        result = collapse_via_quantum_noetic_resonance(machine, lang)
        assert abs(result["rho_resonancia"] - 1.0) < 1e-10

    def test_oracle_sello(self):
        """Oracle result bears the sovereign seal ∴𓂀Ω∞³Φ."""
        machine = self._make_machine()
        lang = Language(name="SAT", is_in_NP=True, decision=lambda x: True)
        result = collapse_via_quantum_noetic_resonance(machine, lang)
        assert result["sello"] == "∴𓂀Ω∞³Φ"

    def test_oracle_insight_mechanism_mentioned(self):
        """Oracle result describes the Insight mechanism."""
        machine = self._make_machine()
        lang = Language(name="SAT", is_in_NP=True, decision=lambda x: True)
        result = collapse_via_quantum_noetic_resonance(machine, lang)
        assert "Oráculo de Insight" in result["mecanismo"]
