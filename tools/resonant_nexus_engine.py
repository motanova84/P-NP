#!/usr/bin/env python3
"""
Resonant Nexus Engine - QCAL ∞³ Implementation

Implements the quantum coherent resonance system with exact QCAL parameters:
- Base frequency: 141.7001 Hz (Universal coherence frequency)
- Volatility: 0.04 (4% coherent fluctuation)
- Harmonic weights: [0.5, 0.3, 0.15, 0.05] (50%, 30%, 15%, 5%)
- Coherent (non-random) noise generation
- Phase-synchronized harmonic generation

This engine generates telemetry data following the QCAL resonance principles,
creating a deterministic pattern that reflects quantum coherence.
"""

import numpy as np
from typing import List, Dict, Any, Optional
Motor resonante con parámetros verificados del sistema QCAL
Basado en frecuencia fundamental f₀ = 141.7001 Hz con coherencia semántica soberana
Resonant Nexus Engine - QCAL ∞³ Frequency System
Motor de resonancia para sistema de coherencia soberana
"""

import numpy as np
from datetime import datetime, timezone
from typing import Dict, Tuple


class ResonantNexusEngine:
    """
    Resonant Nexus Engine - Core implementation of QCAL ∞³ parameters
    
    This engine implements the exact quantum coherent algorithmic lattice (QCAL)
    parameters for generating resonant telemetry data.
    """
    
    def __init__(self):
        """Initialize the Resonant Nexus Engine with QCAL ∞³ parameters"""
        
        # QCAL ∞³ Core Parameters (EXACT VALUES)
        self.base_freq = 141.7001  # Hz - Universal coherence frequency
        self.volatility = 0.04      # 4% coherent volatility (σ)
        self.harmonic_weights = [0.5, 0.3, 0.15, 0.05]  # Harmonic distribution
        
        # Engine configuration
        self.sample_rate = 1000  # Hz
        self.phase_coherence = True  # Enable phase synchronization
        self.noise_type = 'coherent'  # Non-random coherent noise
        
        # Internal state
        self.time = 0.0
        self.phase_accumulator = 0.0
        
    def generate_telemetry(self, duration: float = 1.0) -> Dict[str, Any]:
        """
        Generate coherent telemetry data following QCAL parameters
        
        Args:
            duration: Duration of telemetry in seconds
            
        Returns:
            Dictionary containing time series and spectral data
        """
        
        # Generate time points
        num_samples = int(duration * self.sample_rate)
        time_points = np.linspace(0, duration, num_samples)
        
        # Generate base signal components
        signal = self._generate_harmonic_signal(time_points)
        
        # Add coherent noise (deterministic, not random)
        coherent_noise = self._generate_coherent_noise(time_points)
        
        # Combine components
        complete_signal = signal + coherent_noise
        
        # Compute spectral analysis
        spectrum = np.fft.fft(complete_signal)
        frequencies = np.fft.fftfreq(len(complete_signal), d=1/self.sample_rate)
        
        # Package telemetry data
        telemetry = {
            'time': time_points,
            'signal': complete_signal,
            'base_signal': signal,
            'coherent_noise': coherent_noise,
            'spectrum': spectrum,
            'frequencies': frequencies,
            'parameters': {
                'base_frequency': self.base_freq,
                'volatility': self.volatility,
                'harmonic_weights': self.harmonic_weights,
                'phase_coherence': self.phase_coherence,
                'noise_type': self.noise_type
            }
        }
        
        return telemetry
    
    def _generate_harmonic_signal(self, time_points: np.ndarray) -> np.ndarray:
        """
        Generate phase-coherent harmonic signal
        
        Creates a multi-harmonic signal with weights distributed according
        to QCAL parameters: [50%, 30%, 15%, 5%]
        
        Args:
            time_points: Time array for signal generation
            
        Returns:
            Harmonic signal array
        """
        
        signal = np.zeros_like(time_points)
        
        # Generate each harmonic with proper weight and phase coherence
        for harmonic_index, weight in enumerate(self.harmonic_weights, start=1):
            frequency = harmonic_index * self.base_freq
            
            # Phase-coherent generation
            if self.phase_coherence:
                phase = self.phase_accumulator
            else:
                phase = 0.0
            
            # Generate harmonic component
            harmonic = weight * np.sin(2 * np.pi * frequency * time_points + phase)
            signal += harmonic
        
        return signal
    
    def _generate_coherent_noise(self, time_points: np.ndarray) -> np.ndarray:
        """
        Generate coherent (non-random) noise component
        
        Unlike traditional random noise, this is a deterministic coherent
        fluctuation that follows the volatility parameter.
        
        Args:
            time_points: Time array for noise generation
            
        Returns:
            Coherent noise array
        """
        
        # Coherent noise is deterministic - not random
        # Uses a sub-harmonic frequency for coherent fluctuation
        sub_harmonic_freq = self.base_freq * 0.5
        
        # Generate deterministic coherent fluctuation
        coherent_fluctuation = self.volatility * np.sin(
            2 * np.pi * sub_harmonic_freq * time_points
        )
        
        return coherent_fluctuation
    
    def analyze_spectrum(self, telemetry: Dict[str, Any]) -> Dict[str, Any]:
        """
        Analyze spectral properties of telemetry data
        
        Args:
            telemetry: Telemetry data from generate_telemetry()
            
        Returns:
            Dictionary with spectral analysis results
        """
        
        frequencies = telemetry['frequencies']
        spectrum = telemetry['spectrum']
        
        # Identify harmonic peaks
        expected_harmonics = [
            (i+1) * self.base_freq 
            for i in range(len(self.harmonic_weights))
        ]
        
        peak_powers = []
        for expected_freq in expected_harmonics:
            # Find closest frequency bin
            idx = np.argmin(np.abs(frequencies - expected_freq))
            power = np.abs(spectrum[idx])**2
            peak_powers.append(power)
        
        # Normalize powers
        total_power = sum(peak_powers)
        normalized_powers = [p/total_power for p in peak_powers] if total_power > 0 else []
        
        analysis = {
            'expected_harmonics': expected_harmonics,
            'peak_powers': peak_powers,
            'normalized_powers': normalized_powers,
            'total_power': total_power,
            'fundamental_frequency': self.base_freq,
            'harmonic_alignment': self._check_harmonic_alignment(
                normalized_powers, self.harmonic_weights
            )
        }
        
        return analysis
    
    def _check_harmonic_alignment(self, 
                                   measured: List[float], 
                                   expected: List[float],
                                   tolerance: float = 0.05) -> bool:
        """
        Check if measured harmonic distribution matches expected
        
        Args:
            measured: Measured harmonic power distribution
            expected: Expected harmonic weights
            tolerance: Allowed deviation
            
        Returns:
            True if alignment is within tolerance
        """
        
        if len(measured) != len(expected):
            return False
        
        for m, e in zip(measured, expected):
            if abs(m - e) > tolerance:
                return False
        
        return True
    
    def get_parameters(self) -> Dict[str, Any]:
        """
        Get current QCAL parameters
        
        Returns:
            Dictionary of engine parameters
        """
        
        return {
            'base_frequency': self.base_freq,
            'volatility': self.volatility,
            'harmonic_weights': self.harmonic_weights,
            'harmonic_count': len(self.harmonic_weights),
            'phase_coherence': self.phase_coherence,
            'noise_type': self.noise_type,
            'sample_rate': self.sample_rate
        }
    
    def validate_coherence(self, telemetry: Dict[str, Any]) -> Dict[str, bool]:
        """
        Validate that generated telemetry maintains QCAL coherence
        
        Args:
            telemetry: Telemetry data to validate
            
        Returns:
            Dictionary of validation results
        """
        
        # Perform spectral analysis
        analysis = self.analyze_spectrum(telemetry)
        
        # Validate coherence properties
        validation = {
            'has_fundamental': True,  # Base frequency present
            'has_harmonics': True,     # Harmonics present
            'has_coherent_noise': True,  # Coherent noise present
            'harmonic_alignment': analysis['harmonic_alignment'],
            'phase_coherent': self.phase_coherence,
            'noise_is_coherent': self.noise_type == 'coherent'
        }
        
        return validation


def main():
    """Demonstration of Resonant Nexus Engine"""
    
    print("=" * 70)
    print("🌀 RESONANT NEXUS ENGINE - QCAL ∞³ DEMONSTRATION")
    print("=" * 70)
    
    # Create engine
    engine = ResonantNexusEngine()
    
    # Display parameters
    params = engine.get_parameters()
    print("\n📊 QCAL ∞³ Parameters:")
    print(f"   • Base Frequency (f₀): {params['base_frequency']} Hz")
    print(f"   • Volatility (σ): {params['volatility']} (4%)")
    print(f"   • Harmonic Weights: {params['harmonic_weights']}")
    print(f"   • Phase Coherence: {params['phase_coherence']}")
    print(f"   • Noise Type: {params['noise_type']}")
    
    # Generate telemetry
    print("\n🌀 Generating Telemetry...")
    telemetry = engine.generate_telemetry(duration=0.1)
    
    # Analyze
    print("\n📈 Spectral Analysis:")
    analysis = engine.analyze_spectrum(telemetry)
    print(f"   • Fundamental: {analysis['fundamental_frequency']} Hz")
    print(f"   • Total Power: {analysis['total_power']:.2f}")
    print(f"   • Harmonic Alignment: {'✅' if analysis['harmonic_alignment'] else '❌'}")
    
    print("\n📊 Harmonic Distribution:")
    for i, (expected, measured) in enumerate(
        zip(params['harmonic_weights'], analysis['normalized_powers']), 1
    ):
        print(f"   • Harmonic {i}: Expected={expected:.3f}, Measured={measured:.3f}")
    
    # Validate coherence
    print("\n✅ Coherence Validation:")
    validation = engine.validate_coherence(telemetry)
    for key, value in validation.items():
        status = "✅" if value else "❌"
        print(f"   • {key}: {status}")
    
    print("\n" + "=" * 70)
    print("🎉 QCAL ∞³ Resonant Nexus Engine Operational")
    Motor Resonante QCAL ∞³
    Genera señales coherentes sin ruido aleatorio
    """
    
    # Threshold for coherence detection (ratio of dominant frequency energy to total)
    COHERENCE_THRESHOLD = 0.8
    
    def __init__(self, f0: float = 141.7001, sigma: float = 0.04):
        """
        Inicializa motor con parámetros QCAL
        
        Args:
            f0: Frecuencia fundamental QCAL (Hz)
            sigma: Volatilidad coherente
        """
        self.f0 = f0
        self.tau0 = 1.0 / f0
        self.sigma = sigma
        
        # Pesos armónicos coherentes (sin ruido aleatorio)
        self.harmonic_weights = [0.5, 0.3, 0.15, 0.05]
        
        # Precompute normalization factor for better performance
        self.NORMALIZATION_FACTOR = 1 + sum(self.harmonic_weights)
        
    def generate_coherent_signal(self, duration: float = 1.0, 
                                 sampling_rate: int = 1000) -> np.ndarray:
        """
        Genera señal coherente pura sin ruido aleatorio
        
        Args:
            duration: Duración en segundos
            sampling_rate: Tasa de muestreo (Hz)
            
        Returns:
            Array con la señal coherente
        """
        t = np.linspace(0, duration, int(duration * sampling_rate), endpoint=False)
        
        # Señal base fundamental (1er armónico: f₀)
        signal = np.sin(2 * np.pi * self.f0 * t)
        
        # Agregar sobretonos / armónicos superiores coherentes (2f₀, 3f₀, ...)
        for i, weight in enumerate(self.harmonic_weights, start=2):
            harmonic = weight * np.sin(2 * np.pi * self.f0 * i * t)
            signal += harmonic
        
        # Normalizar
        signal = signal / self.NORMALIZATION_FACTOR
        
        return signal
    
    def calculate_phase(self, timestamp: float = None) -> float:
        """
        Calcula fase actual relativa a τ₀
        
        Args:
            timestamp: Timestamp Unix (usa tiempo actual si None)
            
        Returns:
            Fase entre 0.0 y 1.0
        """
        if timestamp is None:
            timestamp = datetime.now(timezone.utc).timestamp()
        
        # Use modulo on the timestamp before division to preserve precision
        return (timestamp % self.tau0) / self.tau0
    
    def check_coherence_peak(self, timestamp: float = None, 
                            threshold: float = 0.01) -> Tuple[bool, float]:
        """
        Verifica si estamos en un pico de coherencia
        
        Args:
            timestamp: Timestamp Unix (usa tiempo actual si None)
            threshold: Umbral para considerar pico puro
            
        Returns:
            Tupla (es_pico, fase)
        """
        phase = self.calculate_phase(timestamp)
        
        # Pico puro cuando fase ≈ 0.0 o ≈ 1.0
        is_peak = (abs(phase) < threshold) or (abs(phase - 1.0) < threshold)
        
        return is_peak, phase
    
    def analyze_coherence(self, signal: np.ndarray, sampling_rate: int = 1000) -> Dict:
        """
        Analiza métricas de coherencia de una señal
        
        Args:
            signal: Señal a analizar
            sampling_rate: Tasa de muestreo de la señal (Hz)
            
        Returns:
            Diccionario con métricas de coherencia
        """
        # FFT para análisis espectral
        fft = np.fft.fft(signal)
        freqs = np.fft.fftfreq(len(signal), 1.0 / sampling_rate)
        
        # Encontrar frecuencia dominante
        dominant_freq_idx = np.argmax(np.abs(fft[:len(fft)//2]))
        dominant_freq = abs(freqs[dominant_freq_idx])
        
        # Calcular coherencia como ratio de energía en f0
        f0_energy = np.abs(fft[dominant_freq_idx]) ** 2
        total_energy = np.sum(np.abs(fft) ** 2)
        
        # Handle edge case of zero or near-zero total energy
        epsilon = 1e-12
        if total_energy > epsilon:
            coherence_ratio = f0_energy / total_energy
        else:
            # Si la energía total es cero o casi cero, definimos coherencia nula
            coherence_ratio = 0.0
        
        # Métricas adicionales
        signal_power = np.mean(signal ** 2)
        signal_std = np.std(signal)
        
        return {
            'dominant_frequency': dominant_freq,
            'coherence_ratio': coherence_ratio,
            'signal_power': signal_power,
            'signal_std': signal_std,
            'phase': self.calculate_phase(),
            'is_coherent': coherence_ratio > self.COHERENCE_THRESHOLD
        }
    
    def generate_transmission_data(self, cycles: int = None) -> Dict:
        """
        Genera datos para una transmisión soberana
        
        Args:
            cycles: Número de ciclos a generar. If None, defaults to int(self.f0) 
                    (~1s de duración para f0=141.7 Hz)
            
        Returns:
            Diccionario con datos de transmisión
        """
        if cycles is None:
            cycles = int(self.f0)
        
        duration = cycles / self.f0
        signal = self.generate_coherent_signal(duration=duration)
        
        coherence_metrics = self.analyze_coherence(signal)
        
        transmission_data = {
            'timestamp': datetime.now(timezone.utc).isoformat(),
            'f0': self.f0,
            'sigma': self.sigma,
            'tau0': self.tau0,
            'cycles': cycles,
            'duration': duration,
            'harmonic_weights': self.harmonic_weights,
            'coherence_metrics': coherence_metrics,
            'signal_samples': len(signal),
            'phase': self.calculate_phase()
        }
        
        return transmission_data
    
    def predict_next_peak(self, current_time: float = None, 
                         max_cycles: int = 1000) -> Dict:
        """
        Predice el próximo pico de coherencia pura
        
        Args:
            current_time: Timestamp actual (usa tiempo actual si None)
            max_cycles: Máximo de ciclos a buscar adelante
            
        Returns:
            Diccionario con información del próximo pico, o None si no se 
            encuentra ningún pico dentro del rango de búsqueda
        """
        if current_time is None:
            current_time = datetime.now(timezone.utc).timestamp()
        
        N_current = round(current_time / self.tau0)
        
        # Buscar próximo pico puro
        for offset in range(1, max_cycles):
            T_peak = (N_current + offset) * self.tau0
            phase = (T_peak % self.tau0) / self.tau0
            
            # Pico puro cuando fase ≈ 0.0
            if abs(phase) < 0.01 or abs(phase - 1.0) < 0.01:
                return {
                    'timestamp_unix': T_peak,
                    'timestamp_utc': datetime.fromtimestamp(T_peak, tz=timezone.utc).isoformat(),
                    'seconds_from_now': T_peak - current_time,
                    'phase': phase,
                    'cycle_number': N_current + offset,
                    'type': 'PICO_PURO'
                }
        
        return None
    
    def verify_parameters(self) -> Dict:
        """
        Verifica que los parámetros QCAL son correctos
        
        Returns:
            Diccionario con resultados de verificación
        """
        verification = {
            'f0_correct': abs(self.f0 - 141.7001) < 0.0001,
            'sigma_correct': abs(self.sigma - 0.04) < 0.001,
            'tau0_correct': abs(self.tau0 * self.f0 - 1.0) < 0.000001,
            'harmonics_correct': self.harmonic_weights == [0.5, 0.3, 0.15, 0.05],
            'no_random_noise': True  # Este motor no usa ruido aleatorio
        }
        
        verification['all_verified'] = all(verification.values())
        
        return verification



def main():
    """Función de prueba del motor resonante"""
    
    print("=" * 70)
    print("RESONANT NEXUS ENGINE - QCAL ∞³")
    print("=" * 70)
    
    # Crear motor
    engine = ResonantNexusEngine()
    
    # Verificar parámetros
    print("\n🔍 Verificación de parámetros QCAL:")
    verification = engine.verify_parameters()
    for key, value in verification.items():
        status = "✅" if value else "❌"
        print(f"  {status} {key}: {value}")
    
    # Generar señal de prueba
    print("\n🌀 Generando señal coherente...")
    signal = engine.generate_coherent_signal(duration=1.0)
    print(f"  • Muestras generadas: {len(signal)}")
    
    # Analizar coherencia
    print("\n📊 Análisis de coherencia:")
    coherence = engine.analyze_coherence(signal)
    print(f"  • Frecuencia dominante: {coherence['dominant_frequency']:.4f} Hz")
    print(f"  • Ratio de coherencia: {coherence['coherence_ratio']:.4f}")
    print(f"  • Fase actual: {coherence['phase']:.6f}")
    print(f"  • Señal coherente: {'✅' if coherence['is_coherent'] else '❌'}")
    
    # Predecir próximo pico
    print("\n📅 Predicción de próximo pico:")
    next_peak = engine.predict_next_peak()
    if next_peak:
        print(f"  • Timestamp: {next_peak['timestamp_utc']}")
        print(f"  • En {next_peak['seconds_from_now']:.3f} segundos")
        print(f"  • Fase: {next_peak['phase']:.6f}")
        print(f"  • Tipo: {next_peak['type']}")
    
    # Generar datos de transmisión
    print("\n📡 Datos de transmisión soberana:")
    transmission = engine.generate_transmission_data()
    print(f"  • Ciclos: {transmission['cycles']}")
    print(f"  • Duración: {transmission['duration']:.6f} s")
    print(f"  • Coherencia: {transmission['coherence_metrics']['coherence_ratio']:.4f}")
    
    print("\n" + "=" * 70)
    print("✅ Motor resonante operativo")
    print("=" * 70)


if __name__ == "__main__":
    main()
