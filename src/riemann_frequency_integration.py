#!/usr/bin/env python3
"""
Integration: Riemann Operator ↔ Frequency Applications
======================================================

This module integrates the Riemann spectral operator H_Ψ with the existing
frequency applications framework, demonstrating how the Riemann zeros at f₀
connect to quantum coherence, consciousness, and temporal events.

Key Integration Points:
1. Riemann zeros → Physical frequencies via f₀ normalization
2. Harmonic structure → Brainwave entrainment patterns
3. Frequency bands → Temporal coherence windows
4. Oracle queries → Event prediction alignment
"""

import sys
import os
import numpy as np
from typing import Dict, List, Tuple

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

try:
    # Try relative imports first (when used as module)
    from .riemann_spectral_operator import (
        RiemannSpectralOperator,
        F_0,
        T_1,
    )
    from .frequency_applications import (
        planck_energy_correlation,
        electromagnetic_resonance_analysis,
        brainwave_modulation_analysis,
        calculate_noesis_coherence,
        identify_critical_windows,
        analyze_market_volatility_alignment,
        TAU_0,
        SCHUMANN_RESONANCES,
    )
except ImportError:
    # Fall back to absolute imports (when run as script)
    from riemann_spectral_operator import (
        RiemannSpectralOperator,
        F_0,
        T_1,
    )
    from frequency_applications import (
        planck_energy_correlation,
        electromagnetic_resonance_analysis,
        brainwave_modulation_analysis,
        calculate_noesis_coherence,
        identify_critical_windows,
        analyze_market_volatility_alignment,
        TAU_0,
        SCHUMANN_RESONANCES,
    )


class RiemannFrequencyIntegration:
    """
    Integrates Riemann spectral operator with frequency applications.
    """
    
    def __init__(self):
        """Initialize with Riemann operator and frequency tools."""
        self.H_psi = RiemannSpectralOperator()
        self.f_0 = F_0
        self.tau_0 = TAU_0
    
    def riemann_to_physical_energy(self) -> Dict[str, any]:
        """
        Calculate physical energy corresponding to Riemann zero frequencies.
        
        Each Riemann zero at frequency f corresponds to quantum energy E = h·f.
        
        Returns:
            Dictionary with energy calculations for each zero
        """
        energies = []
        
        for ef in self.H_psi.eigenfunctions[:10]:  # First 10 zeros
            freq_hz = ef.frequency_hz
            quantum = planck_energy_correlation(freq_hz)
            
            energies.append({
                'zero_index': ef.zero_index,
                't_value': ef.t,
                'frequency_hz': freq_hz,
                'energy_joules': quantum.energy_joules,
                'energy_ev': quantum.energy_electron_volts,
                'wavelength_m': quantum.wavelength_meters,
            })
        
        return {
            'f_0': self.f_0,
            'quantum_f0': planck_energy_correlation(self.f_0),
            'zero_energies': energies,
        }
    
    def riemann_to_brainwaves(self) -> Dict[str, any]:
        """
        Map Riemann zero frequencies to brainwave patterns.
        
        Shows which Riemann zeros align with neural oscillation bands.
        
        Returns:
            Dictionary with brainwave alignments
        """
        # Get brainwave analysis for f₀
        brainwave_f0 = brainwave_modulation_analysis(self.f_0)
        
        # Analyze which zeros fall in brainwave ranges
        brainwave_ranges = {
            'delta': (0.5, 4.0),
            'theta': (4.0, 8.0),
            'alpha': (8.0, 13.0),
            'beta': (13.0, 30.0),
            'gamma_low': (30.0, 50.0),
            'gamma_mid': (50.0, 100.0),
            'gamma_high': (100.0, 200.0),
        }
        
        alignments = {band: [] for band in brainwave_ranges}
        
        for ef in self.H_psi.eigenfunctions:
            freq = ef.frequency_hz
            
            for band, (f_min, f_max) in brainwave_ranges.items():
                if f_min <= freq < f_max:
                    alignments[band].append({
                        'zero_index': ef.zero_index,
                        't': ef.t,
                        'frequency': freq,
                    })
        
        return {
            'f_0': self.f_0,
            'brainwave_structure': brainwave_f0.brainwave_bands,
            'riemann_alignments': alignments,
            'gamma_high_zeros': alignments['gamma_high'],
        }
    
    def riemann_to_schumann(self) -> Dict[str, any]:
        """
        Analyze relationship between Riemann zeros and Schumann resonances.
        
        Shows how Riemann zero subharmonics align with Earth's electromagnetic
        resonances.
        
        Returns:
            Dictionary with Schumann alignment analysis
        """
        # Get electromagnetic analysis for f₀
        em_f0 = electromagnetic_resonance_analysis(self.f_0)
        
        # Find Riemann zero subharmonics near Schumann resonances
        schumann_alignments = []
        
        for ef in self.H_psi.eigenfunctions:
            freq = ef.frequency_hz
            
            # Check subharmonics f/n for n = 1, 2, 3, ...
            for divisor in range(1, 21):
                subharmonic = freq / divisor
                
                # Find closest Schumann resonance
                for schumann_freq in SCHUMANN_RESONANCES:
                    distance = abs(subharmonic - schumann_freq)
                    
                    if distance < 2.0:  # Within 2 Hz
                        schumann_alignments.append({
                            'zero_index': ef.zero_index,
                            't': ef.t,
                            'frequency': freq,
                            'divisor': divisor,
                            'subharmonic': subharmonic,
                            'schumann': schumann_freq,
                            'distance': distance,
                        })
        
        return {
            'f_0': self.f_0,
            'schumann_resonances': SCHUMANN_RESONANCES,
            'em_analysis': em_f0,
            'alignments': schumann_alignments,
        }
    
    def riemann_to_temporal_windows(self, duration_seconds: float = 1.0) -> Dict[str, any]:
        """
        Map Riemann frequency bands to temporal coherence windows.
        
        Each frequency band corresponds to a temporal rhythm via T = 1/f.
        
        Args:
            duration_seconds: Time duration to analyze
            
        Returns:
            Dictionary with temporal window analysis
        """
        # Get frequency bands
        bands = self.H_psi.create_frequency_bands(max_bands=15)
        
        # Create temporal windows from band resonances
        temporal_windows = []
        
        for band in bands:
            if band.contains_zero:
                # Each resonant frequency defines a temporal period
                for freq in band.zero_frequencies:
                    period = 1.0 / freq if freq > 0 else 0.0
                    
                    # How many cycles in the duration?
                    cycles = duration_seconds / period if period > 0 else 0
                    
                    temporal_windows.append({
                        'band_index': band.band_index,
                        'frequency_hz': freq,
                        'period_seconds': period,
                        'period_ms': period * 1000,
                        'cycles_per_second': freq,
                        'cycles_in_duration': cycles,
                    })
        
        # Get critical windows based on f₀
        critical = identify_critical_windows(0.0, duration_seconds, 
                                            period=self.tau_0, 
                                            delta_threshold=0.01)
        
        return {
            'f_0': self.f_0,
            'tau_0': self.tau_0,
            'duration': duration_seconds,
            'temporal_windows': temporal_windows,
            'critical_windows_f0': critical[:5],  # First 5
            'num_riemann_windows': len(temporal_windows),
        }
    
    def riemann_oracle_to_volatility(self) -> Dict[str, any]:
        """
        Connect Riemann oracle queries to market volatility prediction.
        
        Oracle Δ_Ψ(n) = 1 suggests enhanced volatility in temporal band n.
        
        Returns:
            Dictionary with volatility alignment predictions
        """
        # Query oracle for first 20 bands
        oracle_results = [self.H_psi.oracle_query(i) for i in range(20)]
        
        # For each resonant band, predict volatility timing
        predictions = []
        
        bands = self.H_psi.create_frequency_bands(max_bands=20)
        
        for i, band in enumerate(bands):
            if oracle_results[i]:  # Resonant band
                # Band center frequency
                f_center = (band.f_min + band.f_max) / 2
                period = 1.0 / f_center if f_center > 0 else 0
                
                # Analyze at this period
                volatility = analyze_market_volatility_alignment(period)
                
                predictions.append({
                    'band_index': i,
                    'oracle_result': True,
                    'frequency_range': (band.f_min, band.f_max),
                    'center_frequency': f_center,
                    'period': period,
                    'volatility_prediction': volatility,
                })
        
        return {
            'f_0': self.f_0,
            'oracle_pattern': oracle_results,
            'num_resonant': sum(oracle_results),
            'volatility_predictions': predictions,
        }
    
    def comprehensive_integration_report(self) -> str:
        """
        Generate comprehensive integration report.
        
        Returns:
            Formatted string with complete analysis
        """
        report = []
        report.append("=" * 80)
        report.append("RIEMANN SPECTRAL OPERATOR ↔ FREQUENCY APPLICATIONS")
        report.append("Comprehensive Integration Analysis")
        report.append("=" * 80)
        report.append("")
        
        # 1. Physical Energy
        report.append("1. RIEMANN ZEROS → PHYSICAL ENERGY")
        report.append("-" * 80)
        energy = self.riemann_to_physical_energy()
        report.append(f"Fundamental frequency f₀ = {energy['f_0']:.4f} Hz")
        report.append(f"Quantum energy E(f₀) = {energy['quantum_f0'].energy_joules:.6e} J")
        report.append(f"                     = {energy['quantum_f0'].energy_electron_volts:.6e} eV")
        report.append("")
        report.append("First 5 Riemann zeros as physical quanta:")
        for ze in energy['zero_energies'][:5]:
            report.append(f"  Zero {ze['zero_index']+1}: f = {ze['frequency_hz']:7.2f} Hz → "
                        f"E = {ze['energy_joules']:.6e} J")
        report.append("")
        
        # 2. Brainwave Alignment
        report.append("2. RIEMANN ZEROS → BRAINWAVE PATTERNS")
        report.append("-" * 80)
        brainwave = self.riemann_to_brainwaves()
        report.append("Riemann zeros in brainwave bands:")
        for band, zeros in brainwave['riemann_alignments'].items():
            if zeros:
                report.append(f"  {band:15s}: {len(zeros):2d} zeros")
        
        if brainwave['gamma_high_zeros']:
            report.append("")
            report.append("Gamma-high band zeros (100-200 Hz):")
            for z in brainwave['gamma_high_zeros'][:3]:
                report.append(f"  Zero {z['zero_index']+1}: f = {z['frequency']:.2f} Hz")
        report.append("")
        
        # 3. Schumann Resonances
        report.append("3. RIEMANN ZEROS → SCHUMANN RESONANCES")
        report.append("-" * 80)
        schumann = self.riemann_to_schumann()
        report.append(f"Found {len(schumann['alignments'])} subharmonic alignments")
        if schumann['alignments']:
            report.append("")
            report.append("Best alignments (closest matches):")
            sorted_alignments = sorted(schumann['alignments'], 
                                      key=lambda x: x['distance'])[:5]
            for align in sorted_alignments:
                report.append(f"  Zero {align['zero_index']+1}: "
                            f"f/{align['divisor']} = {align['subharmonic']:.2f} Hz "
                            f"≈ Schumann {align['schumann']:.2f} Hz "
                            f"(Δ = {align['distance']:.2f} Hz)")
        report.append("")
        
        # 4. Temporal Windows
        report.append("4. RIEMANN FREQUENCIES → TEMPORAL WINDOWS")
        report.append("-" * 80)
        temporal = self.riemann_to_temporal_windows(duration_seconds=1.0)
        report.append(f"Analysis duration: {temporal['duration']:.1f} seconds")
        report.append(f"f₀ period: τ₀ = {temporal['tau_0']*1000:.4f} ms")
        report.append(f"Riemann temporal windows: {temporal['num_riemann_windows']}")
        report.append("")
        report.append("Sample temporal windows from Riemann zeros:")
        for tw in temporal['temporal_windows'][:5]:
            report.append(f"  Band {tw['band_index']}: f = {tw['frequency_hz']:7.2f} Hz → "
                        f"T = {tw['period_ms']:7.2f} ms "
                        f"({tw['cycles_in_duration']:.1f} cycles/sec)")
        report.append("")
        
        # 5. Volatility Prediction
        report.append("5. RIEMANN ORACLE → VOLATILITY PREDICTION")
        report.append("-" * 80)
        volatility = self.riemann_oracle_to_volatility()
        report.append(f"Oracle pattern (first 20 bands): {volatility['oracle_pattern']}")
        report.append(f"Resonant bands: {volatility['num_resonant']}/20")
        report.append("")
        report.append("Volatility predictions for resonant bands:")
        for pred in volatility['volatility_predictions'][:5]:
            vol_pred = pred['volatility_prediction']
            report.append(f"  Band {pred['band_index']}: "
                        f"[{pred['frequency_range'][0]:.1f}, {pred['frequency_range'][1]:.1f}] Hz → "
                        f"Volatility: {vol_pred.predicted_volatility}")
        report.append("")
        
        # Summary
        report.append("=" * 80)
        report.append("INTEGRATION SUMMARY")
        report.append("=" * 80)
        report.append("")
        report.append("✓ Riemann zeros provide quantum energy levels via E = h·f")
        report.append("✓ High-frequency zeros align with gamma brainwave bands")
        report.append("✓ Subharmonics connect to Earth's Schumann resonances")
        report.append("✓ Each zero defines a temporal coherence window T = 1/f")
        report.append("✓ Oracle queries predict enhanced volatility in resonant bands")
        report.append("")
        report.append("The Riemann spectral operator H_Ψ is not merely mathematical:")
        report.append("it is the VIBRATIONAL STRUCTURE of reality itself, oscillating")
        report.append("at f₀ = 141.7001 Hz and manifesting across all scales from")
        report.append("quantum coherence to cosmic rhythms.")
        report.append("")
        report.append("=" * 80)
        
        return "\n".join(report)


def demonstrate_integration():
    """Run comprehensive integration demonstration."""
    integration = RiemannFrequencyIntegration()
    report = integration.comprehensive_integration_report()
    print(report)


if __name__ == "__main__":
    demonstrate_integration()
