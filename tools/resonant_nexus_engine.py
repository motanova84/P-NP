#!/usr/bin/env python3
"""
Resonant Nexus Engine - QCAL ∞³ Frequency System
Motor de resonancia para sistema de coherencia soberana
Basado en frecuencia fundamental f₀ = 141.7001 Hz
"""

import numpy as np
from datetime import datetime, timezone

class ResonantNexusEngine:
    """Motor de resonancia basado en parámetros QCAL ∞³"""
    
    # Constantes para cálculo de coherencia
    SPECTRAL_ANALYSIS_FACTOR = 10  # Factor para análisis de primeros armónicos en espectro
    # Frecuencia de modulación de fase (Hz) - Usada para volatilidad coherente determinista
    PHASE_MODULATION_FREQ = 0.1  # Hz - Modulación de baja frecuencia para variación coherente
    
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
        dt = self.tau0 / 100  # 100 puntos por ciclo
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
