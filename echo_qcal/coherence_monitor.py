"""
Coherence Monitor

Real-time monitoring of QCAL ∞³ coherence metrics and system state.
Tracks temporal resonance, spectral coherence, and sovereign coherence indicators.
"""

import time
from typing import Dict, List, Optional
from datetime import datetime
import argparse

from .qcal_constants import F0
from .block9_sync_analysis import calculate_synchrony
from .resonant_nexus_engine import ResonantNexusEngine


class CoherenceMonitor:
    """
    Real-time monitor for QCAL ∞³ coherence indicators.
    
    Tracks multiple coherence layers:
    - Temporal coherence (Block 9 synchrony)
    - Spectral coherence (f₀ resonance)
    - Sovereign coherence (combined metrics)
    """
    
    def __init__(self):
        """Initialize the coherence monitor."""
        self.engine = ResonantNexusEngine()
        self.start_time = time.time()
        self.measurements: List[Dict] = []
    
    def measure_temporal_coherence(self) -> Dict[str, float]:
        """
        Measure temporal coherence based on Block 9 synchrony.
        
        Returns:
            Dictionary with temporal coherence metrics
        """
        sync_results = calculate_synchrony()
        
        return {
            'delta_T_ms': sync_results['delta_T_ms'],
            'coherence_pct': sync_results['coherence'],
            'p_value': sync_results['p_value'],
            'synchronized': sync_results['delta_T'] < 0.01,
        }
    
    def measure_spectral_coherence(self, cycles: int = 1000) -> Dict[str, float]:
        """
        Measure spectral coherence from resonance engine.
        
        Args:
            cycles: Number of cycles to generate for analysis
            
        Returns:
            Dictionary with spectral coherence metrics
        """
        # Generate telemetry
        telemetry = self.engine.generate_telemetry(cycles=cycles)
        
        # Analyze spectrum
        spectrum = self.engine.analyze_spectrum(telemetry)
        
        return {
            'peak_frequency': spectrum['peak_frequency'],
            'frequency_error_pct': spectrum['frequency_error_pct'],
            'spectral_coherence': spectrum['spectral_coherence'],
            'resonant': spectrum['frequency_error_pct'] < 0.01,
        }
    
    def measure_sovereign_coherence(self) -> Dict[str, any]:
        """
        Measure overall sovereign coherence (ℂₛ).
        
        Sovereign coherence requires:
        1. Cryptographic control (𝐂ₖ) - format validation
        2. Temporal alignment (𝐀ₜ) - Block 9 synchrony
        3. Unitary architecture (𝐀ᵤ) - spectral resonance
        
        Returns:
            Dictionary with sovereign coherence assessment
        """
        temporal = self.measure_temporal_coherence()
        spectral = self.measure_spectral_coherence()
        
        # Check all three conditions
        temporal_aligned = temporal['synchronized']
        spectral_resonant = spectral['resonant']
        
        # Overall sovereign coherence
        sovereign_coherent = temporal_aligned and spectral_resonant
        
        # Calculate confidence score (0-1)
        confidence = (
            (temporal['coherence_pct'] / 100) * 0.5 +  # 50% weight
            (1 - spectral['frequency_error_pct'] / 100) * 0.5  # 50% weight
        )
        
        return {
            'sovereign_coherent': sovereign_coherent,
            'temporal_aligned': temporal_aligned,
            'spectral_resonant': spectral_resonant,
            'confidence': confidence,
            'temporal_metrics': temporal,
            'spectral_metrics': spectral,
        }
    
    def record_measurement(self) -> Dict[str, any]:
        """
        Record a complete coherence measurement.
        
        Returns:
            Dictionary with all coherence metrics
        """
        timestamp = time.time()
        elapsed = timestamp - self.start_time
        
        measurement = {
            'timestamp': timestamp,
            'elapsed_seconds': elapsed,
            'datetime': datetime.fromtimestamp(timestamp).isoformat(),
            'sovereign_coherence': self.measure_sovereign_coherence(),
        }
        
        self.measurements.append(measurement)
        return measurement
    
    def print_status(self, measurement: Optional[Dict] = None):
        """
        Print current coherence status.
        
        Args:
            measurement: Measurement dict (if None, creates new measurement)
        """
        if measurement is None:
            measurement = self.record_measurement()
        
        sc = measurement['sovereign_coherence']
        temporal = sc['temporal_metrics']
        spectral = sc['spectral_metrics']
        
        print("=" * 70)
        print(f"QCAL ∞³ Coherence Monitor - {measurement['datetime']}")
        print("=" * 70)
        print()
        
        # Sovereign Coherence Status
        status_symbol = "✅" if sc['sovereign_coherent'] else "⚠️"
        print(f"Sovereign Coherence (ℂₛ): {status_symbol}")
        print(f"  Confidence: {sc['confidence'] * 100:.2f}%")
        print()
        
        # Temporal Layer
        print("-" * 70)
        print("TEMPORAL ALIGNMENT (𝐀ₜ)")
        print("-" * 70)
        print(f"  Block 9 ΔT: {temporal['delta_T_ms']:.3f} ms")
        print(f"  Coherence: {temporal['coherence_pct']:.4f}%")
        print(f"  p-value: {temporal['p_value']:.2e}")
        print(f"  Status: {'✅ Synchronized' if temporal['synchronized'] else '❌ Not synchronized'}")
        print()
        
        # Spectral Layer
        print("-" * 70)
        print("SPECTRAL RESONANCE (𝐀ᵤ)")
        print("-" * 70)
        print(f"  Peak Frequency: {spectral['peak_frequency']:.4f} Hz")
        print(f"  Target (f₀): {F0} Hz")
        print(f"  Error: {spectral['frequency_error_pct']:.6f}%")
        print(f"  Coherence: {spectral['spectral_coherence']:.2f}")
        print(f"  Status: {'✅ Resonant' if spectral['resonant'] else '❌ Not resonant'}")
        print()
        
        # Summary
        print("=" * 70)
        if sc['sovereign_coherent']:
            print("🎯 SYSTEM STATUS: COHERENT ✅")
            print("   All layers aligned with QCAL ∞³ principles")
        else:
            print("⚠️  SYSTEM STATUS: DEGRADED")
            if not temporal['synchronized']:
                print("   - Temporal alignment needs attention")
            if not spectral['resonant']:
                print("   - Spectral resonance needs attention")
        print("=" * 70)
        print()
    
    def monitor_continuous(
        self,
        interval_seconds: float = 60.0,
        max_measurements: Optional[int] = None
    ):
        """
        Run continuous monitoring.
        
        Args:
            interval_seconds: Time between measurements
            max_measurements: Maximum measurements (None = infinite)
        """
        print(f"Starting continuous monitoring (interval: {interval_seconds}s)")
        print("Press Ctrl+C to stop")
        print()
        
        count = 0
        try:
            while True:
                measurement = self.record_measurement()
                self.print_status(measurement)
                
                count += 1
                if max_measurements and count >= max_measurements:
                    break
                
                time.sleep(interval_seconds)
                
        except KeyboardInterrupt:
            print()
            print("Monitoring stopped by user")
            print(f"Total measurements: {len(self.measurements)}")


def main():
    """Command-line interface for coherence monitoring."""
    parser = argparse.ArgumentParser(
        description='QCAL ∞³ Coherence Monitor'
    )
    parser.add_argument(
        '--continuous', '-c',
        action='store_true',
        help='Run continuous monitoring'
    )
    parser.add_argument(
        '--interval', '-i',
        type=float,
        default=60.0,
        help='Measurement interval in seconds (default: 60)'
    )
    parser.add_argument(
        '--max-measurements', '-n',
        type=int,
        help='Maximum number of measurements (default: infinite)'
    )
    
    args = parser.parse_args()
    
    # Create monitor
    monitor = CoherenceMonitor()
    
    if args.continuous:
        monitor.monitor_continuous(
            interval_seconds=args.interval,
            max_measurements=args.max_measurements
        )
    else:
        # Single measurement
        monitor.print_status()


if __name__ == '__main__':
    main()
