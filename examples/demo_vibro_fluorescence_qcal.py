"""
Demo: Vibro-Fluorescence QCAL Experimental Framework
=====================================================

Demonstrates the complete QCAL experimental framework for testing
vibro-fluorescent coupling in biological systems.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from vibro_fluorescence_qcal import (
    OMEGA_0_QCAL, PSI_CRITICO, KAPPA_PI, MAGICICADA_HARMONICS,
    VibroFluorescentCoupling, CoupledProteinOscillator, ExperimentalProtocol,
    psi_input, energia_total, prediccion_resonancia,
    estructura_armonica_lorentziana, umbral_coherencia,
    hipotesis_nula_test, analisis_espectral
)


def demo_coupling_hamiltonian():
    """Demo 1: Vibro-Fluorescent Coupling Hamiltonian"""
    print("\n" + "="*70)
    print("DEMO 1: HAMILTONIANO DE ACOPLAMIENTO VIBRO-FLUORESCENTE")
    print("="*70)
    
    # Create coupling
    coupling = VibroFluorescentCoupling(mu=1.0, Q=0.1, chi2=0.01, chi3=0.001)
    
    # Test different field strengths
    E_values = np.linspace(0, 2, 100)
    H_values = [coupling.H_acoplamiento(E, 0.1) for E in E_values]
    
    print(f"\nParámetros del acoplamiento:")
    print(f"  μ (dipolo): {coupling.mu}")
    print(f"  Q (cuadrupolo): {coupling.Q}")
    print(f"  χ⁽²⁾: {coupling.chi2}")
    print(f"  χ⁽³⁾: {coupling.chi3}")
    
    print(f"\nRango de energías de acoplamiento:")
    print(f"  Mínimo: {min(H_values):.4f}")
    print(f"  Máximo: {max(H_values):.4f}")
    
    # Plot
    plt.figure(figsize=(10, 6))
    plt.plot(E_values, H_values, 'b-', linewidth=2)
    plt.xlabel('Campo Eléctrico E', fontsize=12)
    plt.ylabel('H_acoplamiento', fontsize=12)
    plt.title('Energía de Acoplamiento Vibro-Fluorescente', fontsize=14)
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig('/tmp/coupling_hamiltonian.png', dpi=150)
    print("\n✓ Gráfica guardada: /tmp/coupling_hamiltonian.png")


def demo_input_signal():
    """Demo 2: Input Signal Generation"""
    print("\n" + "="*70)
    print("DEMO 2: SEÑAL DE ENTRADA MODULADA")
    print("="*70)
    
    # Generate signal
    t = np.linspace(0, 0.1, 5000)  # 100ms
    dt = t[1] - t[0]
    
    A0 = 1.0
    m = 0.5
    omega_p = 2.0  # Hz (modulation)
    
    psi = psi_input(t, A0, m, omega_p, OMEGA_0_QCAL)
    E_total = energia_total(psi, dt)
    
    print(f"\nParámetros de la señal:")
    print(f"  A₀ (amplitud): {A0}")
    print(f"  m (modulación): {m}")
    print(f"  ωₚ (modulación): {omega_p} Hz")
    print(f"  ω₀ (portadora QCAL): {OMEGA_0_QCAL} Hz")
    print(f"\nEnergía total: {E_total:.6f}")
    
    # Plot
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 8))
    
    # Time domain
    ax1.plot(t * 1000, psi, 'b-', linewidth=1, alpha=0.7)
    ax1.set_xlabel('Tiempo (ms)', fontsize=12)
    ax1.set_ylabel('Ψ_input(t)', fontsize=12)
    ax1.set_title('Señal de Entrada QCAL Modulada', fontsize=14)
    ax1.grid(True, alpha=0.3)
    
    # Zoom in
    ax2.plot(t[:500] * 1000, psi[:500], 'r-', linewidth=2)
    ax2.set_xlabel('Tiempo (ms)', fontsize=12)
    ax2.set_ylabel('Ψ_input(t)', fontsize=12)
    ax2.set_title('Zoom: Modulación de Amplitud', fontsize=14)
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('/tmp/input_signal.png', dpi=150)
    print("\n✓ Gráfica guardada: /tmp/input_signal.png")


def demo_protein_oscillator():
    """Demo 3: Protein Oscillator Dynamics"""
    print("\n" + "="*70)
    print("DEMO 3: DINÁMICA DEL OSCILADOR PROTEICO")
    print("="*70)
    
    # Create oscillator tuned to QCAL frequency
    omega_qcal = 2 * np.pi * OMEGA_0_QCAL
    m_eff = 1.0
    k_eff = m_eff * omega_qcal**2
    gamma = 0.1 * omega_qcal  # 10% damping
    q = 1.0
    
    osc = CoupledProteinOscillator(m_eff, gamma, k_eff, q)
    
    print(f"\nParámetros del oscilador:")
    print(f"  m_eff: {m_eff}")
    print(f"  k_eff: {k_eff:.2f}")
    print(f"  γ: {gamma:.2f}")
    print(f"  q: {q}")
    print(f"\nFrecuencia de resonancia: {osc.omega_res / (2*np.pi):.4f} Hz")
    print(f"  (Objetivo QCAL: {OMEGA_0_QCAL} Hz)")
    
    # Susceptibility vs frequency
    freqs = np.linspace(100, 200, 1000)
    omegas = 2 * np.pi * freqs
    chi = [osc.susceptibilidad(omega) for omega in omegas]
    chi_mag = np.abs(chi)
    
    # Find peak
    peak_idx = np.argmax(chi_mag)
    peak_freq = freqs[peak_idx]
    
    print(f"\nPico de susceptibilidad en: {peak_freq:.4f} Hz")
    
    # Plot
    plt.figure(figsize=(10, 6))
    plt.plot(freqs, chi_mag, 'b-', linewidth=2)
    plt.axvline(OMEGA_0_QCAL, color='r', linestyle='--', linewidth=2, 
                label=f'QCAL: {OMEGA_0_QCAL} Hz')
    plt.axvline(peak_freq, color='g', linestyle=':', linewidth=2,
                label=f'Pico: {peak_freq:.2f} Hz')
    plt.xlabel('Frecuencia (Hz)', fontsize=12)
    plt.ylabel('|χ(ω)|', fontsize=12)
    plt.title('Susceptibilidad del Oscilador Proteico', fontsize=14)
    plt.legend(fontsize=10)
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig('/tmp/protein_oscillator.png', dpi=150)
    print("\n✓ Gráfica guardada: /tmp/protein_oscillator.png")


def demo_qcal_predictions():
    """Demo 4: QCAL Quantitative Predictions"""
    print("\n" + "="*70)
    print("DEMO 4: PREDICCIONES CUANTITATIVAS QCAL")
    print("="*70)
    
    # Predicción 1: Resonancias
    print("\nPREDICCIÓN 1: Resonancias armónicas")
    test_freqs = [141.7001, 141.7001/2, 141.7001/3, 141.7001*17/13]
    
    for freq in test_freqs:
        pred = prediccion_resonancia(freq, OMEGA_0_QCAL)
        print(f"  ωₚ = {freq:.4f} Hz → Closest: {pred['closest']}, Distance: {pred['min_distance']:.6f}")
    
    # Predicción 2: Estructura armónica
    print("\nPREDICCIÓN 2: Estructura armónica Lorentziana")
    omega_range = np.linspace(50, 500, 2000)
    delta_F = estructura_armonica_lorentziana(omega_range, OMEGA_0_QCAL, k_max=5)
    
    # Find peaks
    from scipy.signal import find_peaks
    peaks, properties = find_peaks(delta_F, height=np.max(delta_F)*0.1, distance=50)
    
    print(f"  Número de picos detectados: {len(peaks)}")
    print(f"  Frecuencias de picos (Hz):")
    for i, peak_idx in enumerate(peaks[:5]):
        print(f"    Pico {i+1}: {omega_range[peak_idx]:.2f} Hz (Armónico {i+1})")
    
    # Predicción 3: Umbral de coherencia
    print("\nPREDICCIÓN 3: Umbral de coherencia Ψ_crítico = 0.888")
    test_psi_values = [0.5, 0.888, 1.0]
    
    for psi in test_psi_values:
        result = umbral_coherencia(psi)
        print(f"  Ψ = {psi:.3f} → Régimen: {result['bifurcation_regime']}, " +
              f"Ratio: {result['ratio']:.3f}")
    
    # Plot harmonic structure
    plt.figure(figsize=(12, 6))
    plt.plot(omega_range, delta_F, 'b-', linewidth=2, alpha=0.7)
    plt.plot(omega_range[peaks], delta_F[peaks], 'ro', markersize=10, 
             label=f'{len(peaks)} picos detectados')
    
    # Mark QCAL harmonics
    for k in range(1, 6):
        plt.axvline(k * OMEGA_0_QCAL, color='gray', linestyle='--', 
                   alpha=0.5, linewidth=1)
    
    plt.xlabel('Frecuencia (Hz)', fontsize=12)
    plt.ylabel('ΔF(ω) [u.a.]', fontsize=12)
    plt.title('Estructura Armónica Lorentziana - Predicción QCAL', fontsize=14)
    plt.legend(fontsize=10)
    plt.grid(True, alpha=0.3)
    plt.xlim(50, 500)
    plt.tight_layout()
    plt.savefig('/tmp/qcal_predictions.png', dpi=150)
    print("\n✓ Gráfica guardada: /tmp/qcal_predictions.png")


def demo_experimental_protocol():
    """Demo 5: Complete Experimental Protocol"""
    print("\n" + "="*70)
    print("DEMO 5: PROTOCOLO EXPERIMENTAL COMPLETO")
    print("="*70)
    
    # Setup protocol
    protocol = ExperimentalProtocol(A0=1.0, m=0.5, omega_0=OMEGA_0_QCAL)
    
    # Frequency sweep around QCAL harmonics
    freq_range = np.concatenate([
        np.linspace(140, 143, 15),  # Around fundamental
        np.linspace(70, 72, 5),     # Around 2nd harmonic
        np.linspace(46, 48, 5)      # Around 3rd harmonic
    ])
    
    print(f"\nBarrido de frecuencias: {len(freq_range)} puntos")
    print(f"  Rango: {freq_range.min():.1f} - {freq_range.max():.1f} Hz")
    
    # Perform sweep
    resultados = protocol.barrido_frecuencia(freq_range, duration=0.05, sample_rate=5000)
    
    # Verify energy conservation
    energias = [resultados[f]["energy"] for f in freq_range]
    print(f"\nConservación de energía:")
    print(f"  Media: {np.mean(energias):.6f}")
    print(f"  Std: {np.std(energias):.6e}")
    print(f"  Variación: {np.std(energias)/np.mean(energias)*100:.6f}%")
    
    # Simulate fluorescence measurements
    print("\nSimulando mediciones de fluorescencia...")
    F0 = 100.0
    
    for freq in freq_range:
        signal = resultados[freq]["signal"]
        t = resultados[freq]["time"]
        
        # Create response with resonance enhancement
        pred = prediccion_resonancia(freq, OMEGA_0_QCAL)
        resonance_factor = 1.0 / (1.0 + 10 * pred["min_distance"])
        
        # Simulated response
        F_response = F0 * (1 + 0.5 * resonance_factor * signal)
        resultados[freq]["F_mean"] = np.mean(F_response)
    
    # QCAL analysis
    analisis = protocol.analisis_qcal(resultados)
    
    print(f"\nAnálisis QCAL:")
    print(f"  F_mean: {analisis['F_mean']:.2f}")
    print(f"  F_std: {analisis['F_std']:.2f}")
    print(f"  Resonancias detectadas: {len(analisis['resonancias_detectadas'])}")
    
    if analisis['resonancias_detectadas']:
        print(f"\n  Resonancias significativas:")
        for res in analisis['resonancias_detectadas']:
            print(f"    Armónico {res['harmonic']}: {res['freq_medida']:.2f} Hz, " +
                  f"R = {res['R_value']:.2f}σ")
    
    print(f"\n  Confirmación QCAL: {'SÍ' if analisis['confirmacion_qcal'] else 'NO'}")
    
    # Plot results
    F_values = [resultados[f]["F_mean"] for f in freq_range]
    R_values = [analisis['R_values'][f] for f in freq_range]
    
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))
    
    # Fluorescence vs frequency
    ax1.plot(freq_range, F_values, 'bo-', linewidth=2, markersize=6, alpha=0.7)
    ax1.axhline(analisis['F_mean'], color='r', linestyle='--', linewidth=2,
               label=f"Media: {analisis['F_mean']:.2f}")
    
    # Mark QCAL harmonics
    for k in [1, 2, 3]:
        ax1.axvline(OMEGA_0_QCAL / k, color='gray', linestyle=':', 
                   linewidth=2, alpha=0.5, label=f'QCAL/{k}')
    
    ax1.set_xlabel('Frecuencia de Modulación (Hz)', fontsize=12)
    ax1.set_ylabel('Fluorescencia Media', fontsize=12)
    ax1.set_title('Respuesta Fluorescente vs Frecuencia', fontsize=14)
    ax1.legend(fontsize=9)
    ax1.grid(True, alpha=0.3)
    
    # R-values (normalized)
    ax2.plot(freq_range, R_values, 'go-', linewidth=2, markersize=6, alpha=0.7)
    ax2.axhline(2.0, color='r', linestyle='--', linewidth=2, label='Umbral 2σ')
    ax2.axhline(-2.0, color='r', linestyle='--', linewidth=2)
    ax2.axhline(0, color='k', linestyle='-', linewidth=1, alpha=0.3)
    
    # Mark QCAL harmonics
    for k in [1, 2, 3]:
        ax2.axvline(OMEGA_0_QCAL / k, color='gray', linestyle=':', 
                   linewidth=2, alpha=0.5)
    
    ax2.set_xlabel('Frecuencia de Modulación (Hz)', fontsize=12)
    ax2.set_ylabel('R(ω) [σ]', fontsize=12)
    ax2.set_title('Análisis QCAL: Desviación Normalizada', fontsize=14)
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('/tmp/experimental_protocol.png', dpi=150)
    print("\n✓ Gráfica guardada: /tmp/experimental_protocol.png")


def demo_falsification_test():
    """Demo 6: Statistical Falsification Test"""
    print("\n" + "="*70)
    print("DEMO 6: TEST ESTADÍSTICO DE FALSACIÓN")
    print("="*70)
    
    # Create mock data with and without QCAL effect
    print("\nEscenario 1: Sin efecto QCAL (H₀ cierta)")
    F_resonante_null = np.random.normal(100, 5, 20)
    F_no_resonante_null = np.random.normal(100, 5, 20)
    
    result_null = hipotesis_nula_test(F_resonante_null, F_no_resonante_null)
    
    print(f"  F-statistic: {result_null['F_statistic']:.4f}")
    print(f"  F-critical (α=0.001): {result_null['F_critical']:.4f}")
    print(f"  p-value: {result_null['p_value']:.6f}")
    print(f"  Rechazar H₀: {result_null['rechazar_H0']}")
    print(f"  Conclusión: {result_null['conclusion']}")
    
    print("\nEscenario 2: Con efecto QCAL fuerte (H₀ falsa)")
    F_resonante_qcal = np.random.normal(150, 5, 20)  # Enhanced at resonance
    F_no_resonante_qcal = np.random.normal(100, 5, 20)  # Normal elsewhere
    
    result_qcal = hipotesis_nula_test(F_resonante_qcal, F_no_resonante_qcal)
    
    print(f"  F-statistic: {result_qcal['F_statistic']:.4f}")
    print(f"  F-critical (α=0.001): {result_qcal['F_critical']:.4f}")
    print(f"  p-value: {result_qcal['p_value']:.6e}")
    print(f"  Rechazar H₀: {result_qcal['rechazar_H0']}")
    print(f"  Conclusión: {result_qcal['conclusion']}")
    
    # Plot comparison
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    # Scenario 1: No QCAL effect
    ax1.boxplot([F_resonante_null, F_no_resonante_null], 
                labels=['Resonante', 'No Resonante'])
    ax1.set_ylabel('Fluorescencia', fontsize=12)
    ax1.set_title(f'Sin Efecto QCAL\nF-stat={result_null["F_statistic"]:.2f}, ' +
                 f'p={result_null["p_value"]:.3f}', fontsize=12)
    ax1.grid(True, alpha=0.3, axis='y')
    
    # Scenario 2: With QCAL effect
    ax2.boxplot([F_resonante_qcal, F_no_resonante_qcal],
                labels=['Resonante', 'No Resonante'])
    ax2.set_ylabel('Fluorescencia', fontsize=12)
    ax2.set_title(f'Con Efecto QCAL\nF-stat={result_qcal["F_statistic"]:.2f}, ' +
                 f'p={result_qcal["p_value"]:.2e}', fontsize=12)
    ax2.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig('/tmp/falsification_test.png', dpi=150)
    print("\n✓ Gráfica guardada: /tmp/falsification_test.png")


def main():
    """Run all demos."""
    print("=" * 70)
    print("DEMOSTRACIÓN: MARCO EXPERIMENTAL QCAL VIBRO-FLUORESCENTE")
    print("=" * 70)
    print(f"\nConstantes Universales:")
    print(f"  Frecuencia QCAL (ω₀): {OMEGA_0_QCAL} Hz")
    print(f"  Umbral crítico (Ψ_c): {PSI_CRITICO}")
    print(f"  Constante κ_Π: {KAPPA_PI}")
    print(f"  Armónicos Magicicada: {MAGICICADA_HARMONICS}")
    
    # Run all demos
    demo_coupling_hamiltonian()
    demo_input_signal()
    demo_protein_oscillator()
    demo_qcal_predictions()
    demo_experimental_protocol()
    demo_falsification_test()
    
    print("\n" + "=" * 70)
    print("DEMOSTRACIÓN COMPLETA")
    print("=" * 70)
    print("\nTodas las gráficas guardadas en /tmp/")
    print("\nFrecuencia: 141.7001 Hz ∞³")
    print("=" * 70)


if __name__ == "__main__":
    main()
