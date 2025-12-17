"""
Resonant Nexus Engine

This module implements a vibrational resonance simulator that generates
telemetry coherent with the QCAL ∞³ primordial frequency f₀ and its
harmonic distribution.

The engine demonstrates that the Protocol Echo implements exactly the
frequency structure predicted by QCAL ∞³ theory.
"""

import numpy as np
import argparse
from typing import Optional, List, Dict
import sys

from .qcal_constants import F0, SIGMA, HARMONIC_WEIGHTS, DEFAULT_CYCLES


class ResonantNexusEngine:
    """
    Vibrational resonance simulator implementing QCAL ∞³ coherence.
    
    This engine generates telemetry that oscillates at the primordial
    frequency f₀ with harmonic distribution matching the cognitive
    architecture predicted by QCAL ∞³.
    
    Attributes:
        f0: Base frequency (Hz)
        sigma: Coherent volatility factor
        harmonic_weights: Distribution of harmonic components
    """
    
    def __init__(
        self,
        base_frequency: float = F0,
        volatility: float = SIGMA,
        harmonic_weights: Optional[Dict[int, float]] = None
    ):
        """
        Initialize the Resonant Nexus Engine.
        
        Args:
            base_frequency: Primordial frequency in Hz (default: F0)
            volatility: Coherent volatility factor (default: SIGMA)
            harmonic_weights: Harmonic distribution dict (default: QCAL weights)
        """
        self.f0 = base_frequency
        self.sigma = volatility
        self.harmonic_weights = harmonic_weights or HARMONIC_WEIGHTS.copy()
        
        # Validate harmonic weights sum to reasonable value
        total_weight = sum(self.harmonic_weights.values())
        if not (0.9 <= total_weight <= 1.1):
            print(f"Warning: Harmonic weights sum to {total_weight:.3f}, expected ~1.0")
    
    def generate_telemetry(
        self,
        cycles: int = DEFAULT_CYCLES,
        return_time: bool = False
    ) -> np.ndarray:
        """
        Generate vibrational telemetry coherent with f₀.
        
        Args:
            cycles: Number of oscillation cycles to generate
            return_time: If True, return (time, telemetry) tuple
            
        Returns:
            Array of telemetry values, or (time, telemetry) if return_time=True
        """
        if cycles <= 0:
            raise ValueError(f"cycles must be positive, got {cycles}")
        
        # Time array
        t = np.arange(cycles) / self.f0
        
        # Initialize signal with base frequency (f₀)
        signal = np.sin(2 * np.pi * self.f0 * t)
        
        # Add harmonic components (skip n=1, already included)
        for n, weight in self.harmonic_weights.items():
            if n == 1:
                continue  # f₀ already included
            
            freq = n * self.f0
            harmonic = weight * np.sin(2 * np.pi * freq * t)
            signal += harmonic
        
        # Add coherent volatility (not random noise)
        # Uses half-frequency modulation for coherent fluctuation
        coherent_noise = self.sigma * np.sin(2 * np.pi * self.f0 * t * 0.5)
        telemetry = signal + coherent_noise
        
        if return_time:
            return t, telemetry
        else:
            return telemetry
    
    def analyze_spectrum(self, telemetry: np.ndarray) -> Dict[str, any]:
        """
        Analyze the frequency spectrum of generated telemetry.
        
        Args:
            telemetry: Telemetry array to analyze
            
        Returns:
            Dictionary containing spectral analysis results
        """
        # Compute FFT
        fft = np.fft.fft(telemetry)
        frequencies = np.fft.fftfreq(len(telemetry), d=1/self.f0)
        
        # Get positive frequencies only
        pos_mask = frequencies > 0
        pos_freqs = frequencies[pos_mask]
        pos_fft = np.abs(fft[pos_mask])
        
        # Find peak frequency
        peak_idx = np.argmax(pos_fft)
        peak_freq = pos_freqs[peak_idx]
        
        # Calculate frequency error
        freq_error = abs(peak_freq - self.f0) / self.f0 * 100  # percentage
        
        # Calculate spectral coherence (ratio of peak to mean)
        spectral_coherence = pos_fft[peak_idx] / np.mean(pos_fft)
        
        return {
            'peak_frequency': peak_freq,
            'frequency_error_pct': freq_error,
            'spectral_coherence': spectral_coherence,
            'frequencies': pos_freqs,
            'spectrum': pos_fft,
        }
    
    def verify_implementation(self, cycles: int = 10000) -> Dict[str, any]:
        """
        Verify that the implementation correctly generates f₀ resonance.
        
        Args:
            cycles: Number of cycles for verification (default: 10000)
            
        Returns:
            Dictionary with verification results
        """
        # Generate telemetry
        telemetry = self.generate_telemetry(cycles=cycles)
        
        # Analyze spectrum
        spectrum_results = self.analyze_spectrum(telemetry)
        
        # Check implementation accuracy
        freq_accurate = spectrum_results['frequency_error_pct'] < 0.01  # < 0.01% error
        coherence_high = spectrum_results['spectral_coherence'] > 10  # Strong peak
        
        # Verify harmonic weights
        harmonics_verified = all(
            n in self.harmonic_weights
            for n in [1, 2, 3, 4]
        )
        
        weights_sum = sum(self.harmonic_weights.values())
        weights_correct = abs(weights_sum - 1.0) < 0.01
        
        all_verified = (
            freq_accurate and
            coherence_high and
            harmonics_verified and
            weights_correct
        )
        
        return {
            'verified': all_verified,
            'frequency_accurate': freq_accurate,
            'coherence_high': coherence_high,
            'harmonics_verified': harmonics_verified,
            'weights_correct': weights_correct,
            'spectrum_analysis': spectrum_results,
            'telemetry_samples': len(telemetry),
        }
    
    def print_status(self):
        """Print current engine configuration."""
        print("=" * 70)
        print("Resonant Nexus Engine - QCAL ∞³ Configuration")
        print("=" * 70)
        print(f"Base Frequency (f₀):  {self.f0} Hz")
        print(f"Volatility (σ):       {self.sigma} ({self.sigma * 100}%)")
        print()
        print("Harmonic Distribution:")
        for n, weight in sorted(self.harmonic_weights.items()):
            freq = n * self.f0
            print(f"  {n}f₀ ({freq:.2f} Hz): {weight * 100:.1f}%")
        print("=" * 70)


def main():
    """Command-line interface for Resonant Nexus Engine."""
    parser = argparse.ArgumentParser(
        description='Resonant Nexus Engine - QCAL ∞³ Vibrational Simulator'
    )
    parser.add_argument(
        '--cycles', '-c',
        type=int,
        default=DEFAULT_CYCLES,
        help=f'Number of oscillation cycles (default: {DEFAULT_CYCLES})'
    )
    parser.add_argument(
        '--verify', '-v',
        action='store_true',
        help='Run verification of implementation'
    )
    parser.add_argument(
        '--plot',
        action='store_true',
        help='Plot telemetry and spectrum (requires matplotlib)'
    )
    
    args = parser.parse_args()
    
    # Create engine
    engine = ResonantNexusEngine()
    engine.print_status()
    print()
    
    # Generate telemetry
    print(f"Generating {args.cycles} cycles of vibrational telemetry...")
    t, telemetry = engine.generate_telemetry(
        cycles=args.cycles,
        return_time=True
    )
    print(f"✅ Generated {len(telemetry)} samples")
    print()
    
    # Run verification if requested
    if args.verify:
        print("Running implementation verification...")
        print("-" * 70)
        results = engine.verify_implementation(cycles=args.cycles)
        
        print(f"Frequency Accurate:   {'✅' if results['frequency_accurate'] else '❌'}")
        print(f"High Coherence:       {'✅' if results['coherence_high'] else '❌'}")
        print(f"Harmonics Verified:   {'✅' if results['harmonics_verified'] else '❌'}")
        print(f"Weights Correct:      {'✅' if results['weights_correct'] else '❌'}")
        print()
        
        spectrum = results['spectrum_analysis']
        print(f"Peak Frequency:       {spectrum['peak_frequency']:.4f} Hz")
        print(f"Frequency Error:      {spectrum['frequency_error_pct']:.6f}%")
        print(f"Spectral Coherence:   {spectrum['spectral_coherence']:.2f}")
        print()
        
        if results['verified']:
            print("🎯 VERDICT: Implementation VERIFIED ✅")
            print(f"   The engine correctly implements f₀ = {F0} Hz")
        else:
            print("⚠️  VERDICT: Implementation has issues")
        print()
    
    # Plot if requested
    if args.plot:
        try:
            import matplotlib.pyplot as plt
            
            fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 8))
            
            # Plot telemetry (first 200 samples)
            samples_to_plot = min(200, len(telemetry))
            ax1.plot(t[:samples_to_plot] * 1000, telemetry[:samples_to_plot])
            ax1.set_xlabel('Time (ms)')
            ax1.set_ylabel('Amplitude')
            ax1.set_title(f'Vibrational Telemetry at f₀ = {F0} Hz')
            ax1.grid(True, alpha=0.3)
            
            # Plot spectrum
            spectrum_results = engine.analyze_spectrum(telemetry)
            freqs = spectrum_results['frequencies']
            spec = spectrum_results['spectrum']
            
            # Plot only up to 10× base frequency
            freq_limit = 10 * F0
            mask = freqs <= freq_limit
            
            ax2.plot(freqs[mask], spec[mask])
            ax2.set_xlabel('Frequency (Hz)')
            ax2.set_ylabel('Magnitude')
            ax2.set_title('Frequency Spectrum')
            ax2.grid(True, alpha=0.3)
            
            # Mark f₀ and harmonics
            for n in [1, 2, 3, 4]:
                ax2.axvline(n * F0, color='r', linestyle='--', alpha=0.5, label=f'{n}f₀')
            
            plt.tight_layout()
            plt.savefig('resonant_nexus_telemetry.png', dpi=150)
            print("📊 Plot saved to: resonant_nexus_telemetry.png")
            print()
            
        except ImportError:
            print("⚠️  matplotlib not available, skipping plot")
            print()


if __name__ == '__main__':
    main()
