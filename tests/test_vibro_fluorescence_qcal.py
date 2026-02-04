"""
Test Suite for Vibro-Fluorescence QCAL Framework
================================================

Tests all components of the vibro-fluorescence coupling experimental framework.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import numpy as np
import pytest
import math

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from vibro_fluorescence_qcal import (
    # Constants
    OMEGA_0_QCAL, PSI_CRITICO, KAPPA_PI, PHI, MAGICICADA_HARMONICS,
    
    # Classes
    VibroFluorescentCoupling, CoupledProteinOscillator, ExperimentalProtocol,
    
    # Functions - Spectral formalism
    psi_input, energia_total, normalize_energy, respuesta_fluorescente,
    parametro_qcal_critico,
    
    # Functions - Resonance
    frecuencia_resonancia_qcal,
    
    # Functions - Fluorescence
    intensidad_fluorescencia_gfp, delta_I_sobre_I0,
    
    # Functions - QCAL predictions
    prediccion_resonancia, estructura_armonica_lorentziana, umbral_coherencia,
    
    # Functions - Falsification
    hipotesis_nula_test,
    
    # Functions - Signal processing
    filtro_gaussiano, analisis_espectral, calcular_snr, criterio_deteccion_positiva,
    
    # Functions - State equation
    ecuacion_estado_qcal
)


class TestConstants:
    """Test universal constants."""
    
    def test_omega_0_qcal(self):
        """Test QCAL carrier frequency."""
        assert OMEGA_0_QCAL == 141.7001
        assert isinstance(OMEGA_0_QCAL, float)
    
    def test_psi_critico(self):
        """Test critical coherence threshold."""
        assert PSI_CRITICO == 0.888
        assert 0 < PSI_CRITICO < 1
    
    def test_kappa_pi(self):
        """Test κ_Π constant."""
        assert KAPPA_PI == 2.578208
        assert abs(KAPPA_PI - 2.5773) < 0.001
    
    def test_phi(self):
        """Test golden ratio."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10
    
    def test_magicicada_harmonics(self):
        """Test Magicicada harmonics list."""
        assert isinstance(MAGICICADA_HARMONICS, list)
        assert 1 in MAGICICADA_HARMONICS
        assert 13 in MAGICICADA_HARMONICS
        assert 17 in MAGICICADA_HARMONICS


class TestVibroFluorescentCoupling:
    """Test Hamiltonian coupling class."""
    
    def test_initialization(self):
        """Test coupling initialization."""
        coupling = VibroFluorescentCoupling(mu=1.0, Q=0.1, chi2=0.01, chi3=0.001)
        assert coupling.mu == 1.0
        assert coupling.Q == 0.1
        assert coupling.chi2 == 0.01
        assert coupling.chi3 == 0.001
    
    def test_H_acoplamiento_linear(self):
        """Test linear coupling terms."""
        coupling = VibroFluorescentCoupling(mu=1.0, Q=0.5, chi2=0.0, chi3=0.0)
        E = 2.0
        grad_E = 0.1
        
        H = coupling.H_acoplamiento(E, grad_E)
        
        # H = μE + Q∇E = 1.0*2.0 + 0.5*0.1 = 2.05
        assert abs(H - 2.05) < 1e-10
    
    def test_H_acoplamiento_nonlinear(self):
        """Test nonlinear coupling terms."""
        coupling = VibroFluorescentCoupling(mu=0.0, Q=0.0, chi2=0.1, chi3=0.01)
        E = 2.0
        grad_E = 0.0
        
        H = coupling.H_acoplamiento(E, grad_E)
        
        # H = χ⁽²⁾E² + χ⁽³⁾E³ = 0.1*4 + 0.01*8 = 0.48
        assert abs(H - 0.48) < 1e-10
    
    def test_H_acoplamiento_full(self):
        """Test full coupling with all terms."""
        coupling = VibroFluorescentCoupling(mu=1.0, Q=0.1, chi2=0.01, chi3=0.001)
        E = 1.0
        grad_E = 1.0
        
        H = coupling.H_acoplamiento(E, grad_E)
        
        # All terms should be positive
        assert H > 0


class TestSpectralFormalism:
    """Test spectral formalism functions."""
    
    def test_psi_input_shape(self):
        """Test input signal shape."""
        t = np.linspace(0, 1, 1000)
        psi = psi_input(t, A0=1.0, m=0.5, omega_p=1.0)
        
        assert len(psi) == len(t)
        assert isinstance(psi, np.ndarray)
    
    def test_psi_input_modulation(self):
        """Test modulation envelope."""
        t = np.linspace(0, 1, 1000)
        
        # Without modulation (m=0)
        psi_no_mod = psi_input(t, A0=1.0, m=0.0, omega_p=1.0)
        
        # With modulation (m=0.5)
        psi_mod = psi_input(t, A0=1.0, m=0.5, omega_p=1.0)
        
        # Modulated signal should have different amplitude
        assert not np.allclose(psi_no_mod, psi_mod)
    
    def test_energia_total_positive(self):
        """Test energy is always positive."""
        t = np.linspace(0, 1, 1000)
        dt = t[1] - t[0]
        psi = psi_input(t, A0=1.0, m=0.5, omega_p=1.0)
        
        E = energia_total(psi, dt)
        
        assert E > 0
    
    def test_energia_total_scaling(self):
        """Test energy scales with amplitude."""
        t = np.linspace(0, 1, 1000)
        dt = t[1] - t[0]
        
        psi1 = psi_input(t, A0=1.0, m=0.5, omega_p=1.0)
        psi2 = psi_input(t, A0=2.0, m=0.5, omega_p=1.0)
        
        E1 = energia_total(psi1, dt)
        E2 = energia_total(psi2, dt)
        
        # E ∝ A²
        assert abs(E2 / E1 - 4.0) < 0.1
    
    def test_normalize_energy(self):
        """Test energy normalization."""
        t = np.linspace(0, 1, 1000)
        dt = t[1] - t[0]
        psi = psi_input(t, A0=1.0, m=0.5, omega_p=1.0)
        
        target_E = 10.0
        psi_norm = normalize_energy(psi, target_E, dt)
        
        E_norm = energia_total(psi_norm, dt)
        
        assert abs(E_norm - target_E) < 1e-6
    
    def test_respuesta_fluorescente_basal(self):
        """Test fluorescent response with no modulation."""
        t = np.linspace(0, 1, 100)
        F0 = 100.0
        
        F = respuesta_fluorescente(t, F0, delta_F=0.0, eta=0.0, omega_p=1.0, phi=0.0)
        
        # Should be constant at F0
        assert np.allclose(F, F0)
    
    def test_respuesta_fluorescente_modulated(self):
        """Test fluorescent response with modulation."""
        t = np.linspace(0, 1, 100)
        F0 = 100.0
        delta_F = 10.0
        eta = 0.5
        
        F = respuesta_fluorescente(t, F0, delta_F, eta, omega_p=1.0, phi=0.0)
        
        # Should oscillate around F0 + delta_F
        assert F.min() < F0 + delta_F
        assert F.max() > F0 + delta_F
    
    def test_parametro_qcal_critico(self):
        """Test critical QCAL parameter."""
        eta = parametro_qcal_critico(delta_F=10.0, dE_domega=2.0)
        
        assert eta == 5.0
    
    def test_parametro_qcal_critico_zero_derivative(self):
        """Test QCAL parameter with zero derivative."""
        eta = parametro_qcal_critico(delta_F=10.0, dE_domega=0.0)
        
        assert eta == 0.0


class TestCoupledProteinOscillator:
    """Test protein oscillator dynamics."""
    
    def test_initialization(self):
        """Test oscillator initialization."""
        osc = CoupledProteinOscillator(m=1.0, gamma=0.1, k=100.0, q=1.0)
        
        assert osc.m == 1.0
        assert osc.gamma == 0.1
        assert osc.k == 100.0
        assert osc.q == 1.0
    
    def test_omega_res_calculation(self):
        """Test resonance frequency calculation."""
        osc = CoupledProteinOscillator(m=1.0, gamma=0.1, k=100.0, q=1.0)
        
        expected_omega = np.sqrt(100.0 / 1.0)
        assert abs(osc.omega_res - expected_omega) < 1e-10
    
    def test_susceptibilidad_at_resonance(self):
        """Test susceptibility at resonance."""
        osc = CoupledProteinOscillator(m=1.0, gamma=0.1, k=100.0, q=1.0)
        
        # At resonance (ω = ω_res), susceptibility should be maximum
        chi_res = osc.susceptibilidad(osc.omega_res)
        chi_off = osc.susceptibilidad(osc.omega_res * 1.5)
        
        # Magnitude at resonance should be larger
        assert abs(chi_res) > abs(chi_off)
    
    def test_respuesta_frecuencia(self):
        """Test frequency response."""
        osc = CoupledProteinOscillator(m=1.0, gamma=0.1, k=100.0, q=1.0)
        
        omega = osc.omega_res
        E_omega = 1.0 + 0j
        
        x = osc.respuesta_frecuencia(omega, E_omega)
        
        assert isinstance(x, complex)
    
    def test_frecuencia_resonancia_qcal(self):
        """Test QCAL resonance frequency calculation."""
        # Find k_eff and m_eff that give 141.7 Hz
        omega_target = 2 * np.pi * 141.7
        m_eff = 1.0
        k_eff = m_eff * omega_target**2
        
        freq = frecuencia_resonancia_qcal(k_eff, m_eff)
        
        assert abs(freq - 141.7) < 0.01


class TestFluorescenceTransduction:
    """Test fluorescence transduction."""
    
    def test_intensidad_fluorescencia_gfp_equilibrium(self):
        """Test GFP intensity at equilibrium."""
        x = np.array([1.0, 2.0, 3.0])
        x0 = np.array([1.0, 2.0, 3.0])
        sigma = np.array([0.1, 0.1, 0.1])
        alpha = np.array([1.0, 1.0, 1.0])
        
        I = intensidad_fluorescencia_gfp(x, x0, sigma, alpha)
        
        # At equilibrium, F = 1, so I = sum(alpha) = 3.0
        assert abs(I - 3.0) < 1e-10
    
    def test_intensidad_fluorescencia_gfp_displaced(self):
        """Test GFP intensity when displaced."""
        x = np.array([2.0, 2.0, 3.0])
        x0 = np.array([1.0, 2.0, 3.0])
        sigma = np.array([0.1, 0.1, 0.1])
        alpha = np.array([1.0, 1.0, 1.0])
        
        I = intensidad_fluorescencia_gfp(x, x0, sigma, alpha)
        
        # Displaced, so I < 3.0
        assert I < 3.0
    
    def test_delta_I_sobre_I0_linear(self):
        """Test intensity change with linear terms only."""
        x_tilde = np.array([1.0 + 0j, 0.5 + 0j, 0.3 + 0j])
        alpha = np.array([1.0, 1.0, 1.0])
        
        delta_I = delta_I_sobre_I0(x_tilde, alpha, beta=None)
        
        # ΔI/I₀ = Σ α|x|² = 1 + 0.25 + 0.09 = 1.34
        expected = 1.0**2 + 0.5**2 + 0.3**2
        assert abs(delta_I - expected) < 1e-10
    
    def test_delta_I_sobre_I0_with_coupling(self):
        """Test intensity change with coupling terms."""
        x_tilde = np.array([1.0 + 0j, 0.5 + 0j])
        alpha = np.array([1.0, 1.0])
        beta = np.array([[0.1, 0.2], [0.2, 0.1]])
        
        delta_I = delta_I_sobre_I0(x_tilde, alpha, beta)
        
        # Should include both linear and coupling terms
        linear = 1.0 + 0.25
        # coupling ≈ 0.1*1 + 0.2*0.5 + 0.2*0.5 + 0.1*0.25
        assert delta_I > linear


class TestQCALPredictions:
    """Test QCAL quantitative predictions."""
    
    def test_prediccion_resonancia_exact(self):
        """Test resonance prediction at exact harmonic."""
        # Test at exactly 1:1 resonance
        pred = prediccion_resonancia(omega_p=141.7001, omega_0=141.7001)
        
        assert pred["1/1"] < 1e-10
        assert pred["closest"] == "1/1"
    
    def test_prediccion_resonancia_harmonic(self):
        """Test resonance prediction at harmonic."""
        # Test at 2:1 harmonic (double frequency)
        pred = prediccion_resonancia(omega_p=2 * 141.7001, omega_0=141.7001)
        
        assert pred["2/1"] < 1e-10
        assert pred["closest"] == "2/1"
    
    def test_prediccion_resonancia_magicicada(self):
        """Test Magicicada 17/13 resonance."""
        omega_0 = 141.7001
        omega_p = omega_0 * 17 / 13
        
        pred = prediccion_resonancia(omega_p, omega_0)
        
        assert pred["17/13"] < 0.01
    
    def test_estructura_armonica_lorentziana_shape(self):
        """Test Lorentzian harmonic structure shape."""
        omega = np.linspace(100, 200, 1000)
        delta_F = estructura_armonica_lorentziana(omega, omega_0=141.7001, k_max=3)
        
        assert len(delta_F) == len(omega)
        assert np.all(delta_F >= 0)
    
    def test_estructura_armonica_lorentziana_peaks(self):
        """Test that Lorentzian has peaks at harmonics."""
        omega = np.linspace(100, 500, 5000)
        omega_0 = 141.7001
        delta_F = estructura_armonica_lorentziana(omega, omega_0=omega_0, k_max=3)
        
        # Find peaks
        from scipy.signal import find_peaks
        peaks, _ = find_peaks(delta_F, height=np.max(delta_F) * 0.1)
        
        # Should have peaks near harmonics
        assert len(peaks) >= 3
    
    def test_umbral_coherencia_below(self):
        """Test coherence below threshold."""
        result = umbral_coherencia(psi=0.5, psi_critico=0.888)
        
        assert result["above_threshold"] == False
        assert result["bifurcation_regime"] == "incoherent"
        assert result["ratio"] < 1.0
    
    def test_umbral_coherencia_above(self):
        """Test coherence above threshold."""
        result = umbral_coherencia(psi=0.95, psi_critico=0.888)
        
        assert result["above_threshold"] == True
        assert result["bifurcation_regime"] == "coherent"
        assert result["ratio"] > 1.0


class TestExperimentalProtocol:
    """Test experimental protocol class."""
    
    def test_initialization(self):
        """Test protocol initialization."""
        protocol = ExperimentalProtocol(A0=1.0, m=0.5, omega_0=141.7001)
        
        assert protocol.A0 == 1.0
        assert protocol.m == 0.5
        assert protocol.omega_0 == 141.7001
    
    def test_barrido_frecuencia_energy_conservation(self):
        """Test frequency sweep conserves energy."""
        protocol = ExperimentalProtocol(A0=1.0, m=0.5)
        
        freq_range = np.array([1.0, 2.0, 3.0])
        resultados = protocol.barrido_frecuencia(freq_range, duration=0.1, sample_rate=1000)
        
        # All energies should be equal
        energias = [resultados[f]["energy"] for f in freq_range]
        assert np.std(energias) < 1e-6
    
    def test_barrido_frecuencia_output_structure(self):
        """Test frequency sweep output structure."""
        protocol = ExperimentalProtocol()
        
        freq_range = np.array([1.0, 2.0])
        resultados = protocol.barrido_frecuencia(freq_range, duration=0.1, sample_rate=1000)
        
        for freq in freq_range:
            assert freq in resultados
            assert "signal" in resultados[freq]
            assert "energy" in resultados[freq]
            assert "time" in resultados[freq]
    
    def test_medir_fluorescencia_output(self):
        """Test fluorescence measurement output."""
        protocol = ExperimentalProtocol()
        
        t = np.linspace(0, 1, 100)
        signal = np.sin(2 * np.pi * t)
        
        medicion = protocol.medir_fluorescencia(signal, t)
        
        assert "fluorescence" in medicion
        assert "F_mean" in medicion
        assert "F_std" in medicion
        assert "correlation" in medicion
        assert "phase" in medicion
    
    def test_analisis_qcal_structure(self):
        """Test QCAL analysis output structure."""
        protocol = ExperimentalProtocol()
        
        # Create mock results
        freq_range = np.linspace(1, 10, 20)
        resultados_freq = {f: {"F_mean": 100 + np.random.randn()} for f in freq_range}
        
        analisis = protocol.analisis_qcal(resultados_freq)
        
        assert "R_values" in analisis
        assert "F_mean" in analisis
        assert "F_std" in analisis
        assert "resonancias_detectadas" in analisis
        assert "confirmacion_qcal" in analisis


class TestFalsificationControls:
    """Test falsification statistical controls."""
    
    def test_hipotesis_nula_test_no_difference(self):
        """Test null hypothesis when groups are identical."""
        F_res = np.array([100.0, 101.0, 99.0, 100.5])
        F_no_res = np.array([100.5, 99.5, 100.0, 101.0])
        
        result = hipotesis_nula_test(F_res, F_no_res)
        
        # Should not reject H0
        assert result["rechazar_H0"] == False
        assert result["p_value"] > 0.001
    
    def test_hipotesis_nula_test_clear_difference(self):
        """Test null hypothesis when groups differ significantly."""
        F_res = np.array([150.0, 151.0, 149.0, 150.5])
        F_no_res = np.array([100.0, 101.0, 99.0, 100.5])
        
        result = hipotesis_nula_test(F_res, F_no_res)
        
        # Should reject H0
        assert result["rechazar_H0"] == True
        assert result["p_value"] < 0.001
    
    def test_hipotesis_nula_test_structure(self):
        """Test null hypothesis test output structure."""
        F_res = np.array([100.0, 101.0])
        F_no_res = np.array([100.0, 101.0])
        
        result = hipotesis_nula_test(F_res, F_no_res)
        
        assert "F_statistic" in result
        assert "F_critical" in result
        assert "p_value" in result
        assert "df1" in result
        assert "df2" in result
        assert "rechazar_H0" in result
        assert "conclusion" in result


class TestSignalProcessing:
    """Test signal processing functions."""
    
    def test_filtro_gaussiano_shape(self):
        """Test Gaussian filter preserves shape."""
        F_raw = np.random.randn(100)
        t = np.linspace(-5, 5, 100)
        tau = 1.0
        
        F_filtered = filtro_gaussiano(F_raw, t, tau)
        
        assert len(F_filtered) == len(F_raw)
    
    def test_filtro_gaussiano_center_maximum(self):
        """Test Gaussian filter maximizes at center."""
        F_raw = np.ones(100)
        t = np.linspace(-5, 5, 100)
        tau = 1.0
        
        F_filtered = filtro_gaussiano(F_raw, t, tau)
        
        # Center should have maximum value
        center_idx = len(F_filtered) // 2
        assert F_filtered[center_idx] >= F_filtered[0]
        assert F_filtered[center_idx] >= F_filtered[-1]
    
    def test_analisis_espectral_structure(self):
        """Test spectral analysis output structure."""
        F = np.sin(2 * np.pi * 10 * np.linspace(0, 1, 1000))
        dt = 0.001
        
        result = analisis_espectral(F, dt)
        
        assert "frequencies" in result
        assert "fft" in result
        assert "power_spectrum" in result
        assert "peak_freq" in result
    
    def test_analisis_espectral_peak_detection(self):
        """Test spectral analysis detects peak frequency."""
        freq_signal = 10.0  # Hz
        t = np.linspace(0, 1, 1000)
        dt = t[1] - t[0]
        F = np.sin(2 * np.pi * freq_signal * t)
        
        result = analisis_espectral(F, dt)
        
        # Peak should be near 10 Hz
        assert abs(result["peak_freq"] - freq_signal) < 1.0
    
    def test_calcular_snr_high_signal(self):
        """Test SNR calculation with high signal."""
        freqs = np.linspace(0, 100, 1000)
        F_spectral = np.ones(1000) * 0.1
        
        # Add strong peak at 50 Hz
        peak_idx = np.argmin(np.abs(freqs - 50))
        F_spectral[peak_idx] = 10.0
        
        snr = calcular_snr(F_spectral, omega_p=50.0, freqs=freqs)
        
        assert snr > 10
    
    def test_calcular_snr_low_signal(self):
        """Test SNR calculation with low signal."""
        freqs = np.linspace(0, 100, 1000)
        F_spectral = np.ones(1000)
        
        snr = calcular_snr(F_spectral, omega_p=50.0, freqs=freqs)
        
        assert snr < 10
    
    def test_criterio_deteccion_positiva_pass(self):
        """Test detection criterion passes."""
        result = criterio_deteccion_positiva(snr=5.0, coherencia=0.8)
        
        assert result["deteccion_positiva"] == True
        assert result["snr_ok"] == True
        assert result["coherencia_ok"] == True
    
    def test_criterio_deteccion_positiva_fail_snr(self):
        """Test detection criterion fails on SNR."""
        result = criterio_deteccion_positiva(snr=2.0, coherencia=0.8)
        
        assert result["deteccion_positiva"] == False
        assert result["snr_ok"] == False
        assert result["coherencia_ok"] == True
    
    def test_criterio_deteccion_positiva_fail_coherencia(self):
        """Test detection criterion fails on coherence."""
        result = criterio_deteccion_positiva(snr=5.0, coherencia=0.5)
        
        assert result["deteccion_positiva"] == False
        assert result["snr_ok"] == True
        assert result["coherencia_ok"] == False


class TestStateEquation:
    """Test QCAL state equation."""
    
    def test_ecuacion_estado_qcal_shape(self):
        """Test state equation output shape."""
        t = np.linspace(0, 1, 100)
        F = np.ones(100) * 100
        psi = np.sin(2 * np.pi * t)
        
        dFdt = ecuacion_estado_qcal(F, psi, t)
        
        assert len(dFdt) == len(F)
    
    def test_ecuacion_estado_qcal_coupling_dominates(self):
        """Test that coupling term dominates when κ >> γ."""
        t = np.linspace(0, 1, 100)
        F = np.ones(100) * 100
        psi = np.ones(100) * 2.0
        
        # κ >> γ
        dFdt = ecuacion_estado_qcal(F, psi, t, D=1.0, gamma=0.1, kappa=10.0)
        
        # Coupling term should be dominant (positive and large)
        # κ|ψ|² = 10 * 4 = 40 >> γF = 0.1 * 100 = 10
        assert np.mean(dFdt) > 0


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_complete_qcal_experiment_workflow(self):
        """Test complete QCAL experimental workflow."""
        # 1. Setup
        protocol = ExperimentalProtocol(A0=1.0, m=0.5)
        
        # 2. Frequency sweep
        freq_range = np.array([140.0, 141.7001, 143.0])
        resultados = protocol.barrido_frecuencia(freq_range, duration=0.1, sample_rate=1000)
        
        # 3. Mock measurements
        for freq in freq_range:
            signal = resultados[freq]["signal"]
            t = resultados[freq]["time"]
            medicion = protocol.medir_fluorescencia(signal, t)
            resultados[freq]["F_mean"] = medicion["F_mean"]
        
        # 4. QCAL analysis
        analisis = protocol.analisis_qcal(resultados)
        
        # Verify workflow completes
        assert "R_values" in analisis
        assert "confirmacion_qcal" in analisis
    
    def test_resonance_prediction_and_detection(self):
        """Test resonance prediction matches detection."""
        # Predict resonance at QCAL frequency
        pred = prediccion_resonancia(omega_p=141.7001, omega_0=141.7001)
        
        # Should be at exact 1:1 resonance
        assert pred["closest"] == "1/1"
        assert pred["min_distance"] < 1e-10
    
    def test_falsification_workflow(self):
        """Test falsification statistical workflow."""
        # Create mock data with clear difference
        F_resonante = np.array([150.0] * 10) + np.random.randn(10)
        F_no_resonante = np.array([100.0] * 10) + np.random.randn(10)
        
        # Run test
        result = hipotesis_nula_test(F_resonante, F_no_resonante)
        
        # Should detect difference
        assert result["rechazar_H0"] == True
        assert "conclusion" in result


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Vibro-Fluorescence QCAL Framework")
    print("=" * 70)
    print()
    print(f"QCAL Frequency: {OMEGA_0_QCAL} Hz")
    print(f"Critical Threshold Ψ: {PSI_CRITICO}")
    print(f"Constant κ_Π: {KAPPA_PI}")
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    print()
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
