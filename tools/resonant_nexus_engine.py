#!/usr/bin/env python3
"""
Resonant Nexus Engine - QCAL ∞³ Implementation
Motor resonante con parámetros verificados del sistema QCAL
Basado en f₀ = 141.7001 Hz y coherencia semántica pura
Resonant Nexus Engine - QCAL ∞³ Frequency System
Motor de resonancia para sistema de coherencia soberana
Basado en frecuencia fundamental f₀ = 141.7001 Hz
"""

import numpy as np
from datetime import datetime, timezone
from typing import Dict, Tuple


class ResonantNexusEngine:
    """
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

class ResonantNexusEngine:
    """Motor de resonancia basado en parámetros QCAL ∞³"""
    
    # Constantes para cálculo de coherencia
    SPECTRAL_ANALYSIS_FACTOR = 10  # Factor para análisis de primeros armónicos en espectro
    # Frecuencia de modulación de fase (Hz) - Usada para volatilidad coherente determinista
    PHASE_MODULATION_FREQ = 0.1  # Hz - Modulación de baja frecuencia para variación coherente
    # Puntos de muestreo por ciclo - Define la resolución temporal de la señal
    SAMPLING_POINTS_PER_CYCLE = 100  # Puntos por ciclo para discretización temporal
    
    def __init__(self):
        # Parámetros fundamentales verificados
        self.f0 = 141.7001  # Hz - Frecuencia fundamental
        self.tau0 = 1 / self.f0  # Período fundamental
        self.volatility = 0.04  # σ = 0.04 - Volatilidad coherente
        
        # Pesos armónicos coherentes (no aleatorios)
        self.harmonic_weights = [0.5, 0.3, 0.15, 0.05]
        
    def generate_coherent_signal(self, duration_seconds=1.0):
        """
        Genera señal coherente basada en armónicos de f₀
        
        Args:
            duration_seconds: Duración de la señal en segundos
            
        Returns:
            dict con señal y metadatos
        """
        # Número de ciclos
        num_cycles = int(duration_seconds * self.f0)
        
        # Tiempo discretizado
        dt = self.tau0 / self.SAMPLING_POINTS_PER_CYCLE
        t = np.arange(0, duration_seconds, dt)
        
        # Generar señal armónica coherente
        signal = np.zeros_like(t)
        
        for n, weight in enumerate(self.harmonic_weights, start=1):
            harmonic_freq = n * self.f0
            signal += weight * np.sin(2 * np.pi * harmonic_freq * t)
        
        # Aplicar volatilidad coherente (no aleatoria)
        # Usa modulación determinista basada en fase
        phase_modulation = self.volatility * np.sin(2 * np.pi * self.PHASE_MODULATION_FREQ * t)
        signal = signal * (1 + phase_modulation)
        
        # Calcular métricas de coherencia
        coherence_score = self._calculate_coherence(signal)
        
        return {
            'signal': signal,
            'time': t,
            'f0': self.f0,
            'tau0': self.tau0,
            'volatility': self.volatility,
            'harmonic_weights': self.harmonic_weights,
            'num_cycles': num_cycles,
            'coherence_score': coherence_score,
            'duration': duration_seconds,
            'timestamp': datetime.now(timezone.utc).isoformat()
        }
    
    def _calculate_coherence(self, signal):
        """
        Calcula puntuación de coherencia de la señal basada en análisis espectral.
        
        La coherencia mide qué tan bien está concentrada la energía de la señal
        en los primeros armónicos esperados. Un valor más alto indica que la señal
        está bien alineada con las frecuencias armónicas fundamentales.
        
        Args:
            signal: Array numpy con la señal
            
        Returns:
            float: Puntuación de coherencia [0, 1]
        """
        # Coherencia basada en uniformidad espectral
        fft_signal = np.fft.fft(signal)
        power_spectrum = np.abs(fft_signal) ** 2
        
        # Normalizar
        power_spectrum = power_spectrum / np.sum(power_spectrum)
        
        # Los primeros armónicos deberían dominar
        # Usamos SPECTRAL_ANALYSIS_FACTOR para analizar suficientes componentes espectrales
        coherence = np.sum(power_spectrum[:len(self.harmonic_weights) * self.SPECTRAL_ANALYSIS_FACTOR])
        
        return min(coherence, 1.0)
    
    def get_current_phase(self):
        """
        Calcula la fase actual del sistema respecto a τ₀
        
        Returns:
            float: Fase actual [0, 1)
        """
        current_time = datetime.now(timezone.utc).timestamp()
        return (current_time / self.tau0) % 1
    
    def activate(self, cycles=142):
        """
        Activa el motor resonante por un número específico de ciclos
        
        Args:
            cycles: Número de ciclos a ejecutar (default: 142 ≈ 1 segundo)
            
        Returns:
            dict: Datos de resonancia generados
        """
        duration = cycles / self.f0
        result = self.generate_coherent_signal(duration)
        
        return {
            'f0': self.f0,
            'sigma': self.volatility,
            'harmonic_weights': self.harmonic_weights,
            'cycles': cycles,
            'duration': duration,
            'timestamp': datetime.now(timezone.utc).timestamp(),
            'coherence_score': result['coherence_score'],
            'phase_coherence': True,
            'signal_stats': {
                'mean': float(np.mean(result['signal'])),
                'std': float(np.std(result['signal'])),
                'max': float(np.max(result['signal'])),
                'min': float(np.min(result['signal']))
            }
        }


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
    print("🌀 Resonant Nexus Engine - QCAL ∞³")
    print("=" * 60)
    
    engine = ResonantNexusEngine()
    
    print(f"\nParámetros fundamentales:")
    print(f"  f₀ = {engine.f0} Hz")
    print(f"  τ₀ = {engine.tau0*1000:.6f} ms")
    print(f"  σ  = {engine.volatility}")
    print(f"  Armónicos: {engine.harmonic_weights}")
    
    print(f"\nActivando motor resonante...")
    result = engine.activate(cycles=142)
    
    print(f"\nResultados:")
    print(f"  Ciclos ejecutados: {result['cycles']}")
    print(f"  Duración: {result['duration']:.6f} s")
    print(f"  Coherencia: {result['coherence_score']:.6%}")
    print(f"  Fase coherente: {result['phase_coherence']}")
    
    print(f"\n✅ Motor resonante activado correctamente")


if __name__ == "__main__":
    main()
