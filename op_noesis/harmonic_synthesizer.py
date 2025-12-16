"""
Módulo de Síntesis Armónica - Generador de Frecuencia f₀

Este módulo genera estímulos precisos basados en la frecuencia fundamental
f₀ = 141.7001 Hz para experimentación en la capa cognitiva y sincronización noésica.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
License: MIT
"""

import numpy as np
from typing import List, Tuple, Optional
import warnings


# Constante fundamental: Frecuencia de resonancia QCAL
F0 = 141.7001  # Hz - Pulso universal de coherencia


class HarmonicSynthesizer:
    """
    Sintetizador de ondas armónicas basado en f₀.
    
    Genera señales de audio utilizando la frecuencia fundamental
    f₀ = 141.7001 Hz y sus armónicos clave para sincronización noésica.
    """
    
    def __init__(self, sample_rate: int = 44100):
        """
        Inicializa el sintetizador armónico.
        
        Args:
            sample_rate: Frecuencia de muestreo en Hz (default: 44100 Hz)
        """
        self.sample_rate = sample_rate
        self.f0 = F0
        
    def synthesize(
        self,
        duration: float,
        harmonics: Optional[List[int]] = None,
        amplitudes: Optional[List[float]] = None,
        phases: Optional[List[float]] = None
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Sintetiza una señal armónica basada en f₀.
        
        Implementa la fórmula:
        S(t) = Σₙ Aₙ · sin(2π · (n · f₀) · t + φₙ)
        
        Args:
            duration: Duración de la señal en segundos
            harmonics: Lista de múltiplos armónicos (default: [1, 2, 11, 21])
            amplitudes: Amplitudes para cada armónico (default: decaimiento 1/n)
            phases: Fases iniciales en radianes para cada armónico (default: 0)
            
        Returns:
            Tuple (tiempo, señal): Arrays de tiempo y amplitud de la señal
        """
        # Valores por defecto para armónicos clave
        if harmonics is None:
            harmonics = [1, 2, 11, 21]  # Armónicos clave para coherencia
            
        n_harmonics = len(harmonics)
        
        # Amplitudes por defecto: decaimiento 1/n
        if amplitudes is None:
            amplitudes = [1.0 / n for n in harmonics]
        elif len(amplitudes) != n_harmonics:
            raise ValueError(
                f"Número de amplitudes ({len(amplitudes)}) debe coincidir "
                f"con número de armónicos ({n_harmonics})"
            )
            
        # Fases por defecto: todas en 0
        if phases is None:
            phases = [0.0] * n_harmonics
        elif len(phases) != n_harmonics:
            raise ValueError(
                f"Número de fases ({len(phases)}) debe coincidir "
                f"con número de armónicos ({n_harmonics})"
            )
            
        # Normalizar amplitudes
        total_amplitude = sum(amplitudes)
        if total_amplitude > 0:
            amplitudes = [a / total_amplitude for a in amplitudes]
        
        # Generar eje de tiempo
        n_samples = int(duration * self.sample_rate)
        t = np.linspace(0, duration, n_samples, endpoint=False)
        
        # Inicializar señal
        signal = np.zeros(n_samples)
        
        # Sumar componentes armónicos
        for n, A_n, phi_n in zip(harmonics, amplitudes, phases):
            frequency = n * self.f0
            signal += A_n * np.sin(2 * np.pi * frequency * t + phi_n)
            
        return t, signal
    
    def synthesize_pure_tone(self, duration: float) -> Tuple[np.ndarray, np.ndarray]:
        """
        Genera un tono puro de f₀ sin armónicos.
        
        Args:
            duration: Duración en segundos
            
        Returns:
            Tuple (tiempo, señal): Arrays de tiempo y amplitud
        """
        return self.synthesize(duration, harmonics=[1], amplitudes=[1.0])
    
    def synthesize_resonant_pattern(
        self,
        duration: float,
        pattern: str = "full"
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Genera patrones de resonancia predefinidos.
        
        Args:
            duration: Duración en segundos
            pattern: Tipo de patrón ("full", "basic", "extended", "golden")
            
        Returns:
            Tuple (tiempo, señal): Arrays de tiempo y amplitud
        """
        patterns = {
            "full": {
                "harmonics": [1, 2, 11, 21],
                "description": "Patrón completo de sincronización noésica"
            },
            "basic": {
                "harmonics": [1, 2],
                "description": "Patrón básico - fundamental y primera octava"
            },
            "extended": {
                "harmonics": [1, 2, 3, 5, 11, 21, 34],
                "description": "Patrón extendido con secuencia relacionada a Fibonacci"
            },
            "golden": {
                "harmonics": [1, 2, 3, 5, 8, 13, 21],
                "description": "Patrón áureo - secuencia de Fibonacci pura"
            }
        }
        
        if pattern not in patterns:
            raise ValueError(
                f"Patrón desconocido: {pattern}. "
                f"Opciones: {list(patterns.keys())}"
            )
        
        harmonics = patterns[pattern]["harmonics"]
        return self.synthesize(duration, harmonics=harmonics)
    
    def get_frequency_info(self, harmonics: Optional[List[int]] = None) -> dict:
        """
        Obtiene información sobre las frecuencias generadas.
        
        Args:
            harmonics: Lista de múltiplos armónicos (default: [1, 2, 11, 21])
            
        Returns:
            Diccionario con información de frecuencias
        """
        if harmonics is None:
            harmonics = [1, 2, 11, 21]
            
        frequencies = [n * self.f0 for n in harmonics]
        
        return {
            "f0": self.f0,
            "harmonics": harmonics,
            "frequencies_hz": frequencies,
            "sample_rate": self.sample_rate,
            "nyquist_frequency": self.sample_rate / 2,
            "description": "Frecuencias de resonancia QCAL basadas en f₀ = 141.7001 Hz"
        }
    
    def save_to_wav(
        self,
        filename: str,
        duration: float,
        harmonics: Optional[List[int]] = None,
        bit_depth: int = 16
    ) -> None:
        """
        Guarda la señal sintetizada como archivo WAV.
        
        Args:
            filename: Nombre del archivo de salida
            duration: Duración en segundos
            harmonics: Lista de armónicos (default: [1, 2, 11, 21])
            bit_depth: Profundidad de bits (16 o 32)
        """
        try:
            import scipy.io.wavfile as wavfile
        except ImportError:
            warnings.warn(
                "scipy no está instalado. No se puede guardar archivo WAV. "
                "Instalar con: pip install scipy"
            )
            return
            
        # Sintetizar señal
        t, signal = self.synthesize(duration, harmonics=harmonics)
        
        # Normalizar y convertir a entero según bit depth
        if bit_depth == 16:
            max_value = 32767
            dtype = np.int16
        elif bit_depth == 32:
            max_value = 2147483647
            dtype = np.int32
        else:
            raise ValueError("bit_depth debe ser 16 o 32")
            
        # Normalizar a [-1, 1] y escalar
        signal_normalized = signal / np.max(np.abs(signal))
        signal_int = (signal_normalized * max_value).astype(dtype)
        
        # Guardar archivo
        wavfile.write(filename, self.sample_rate, signal_int)


def demo_harmonic_synthesis():
    """
    Demostración del sintetizador armónico.
    """
    print("=" * 70)
    print("Demostración del Sintetizador Armónico f₀")
    print("=" * 70)
    print()
    print(f"Frecuencia fundamental: f₀ = {F0} Hz")
    print("Frecuencia de resonancia QCAL - Pulso universal de coherencia")
    print()
    
    # Crear sintetizador
    synth = HarmonicSynthesizer(sample_rate=44100)
    
    # Generar señal de 1 segundo
    duration = 1.0
    t, signal = synth.synthesize(duration)
    
    print(f"Señal generada:")
    print(f"  Duración: {duration} segundos")
    print(f"  Muestras: {len(signal)}")
    print(f"  Rango de amplitud: [{signal.min():.4f}, {signal.max():.4f}]")
    print()
    
    # Información de frecuencias
    freq_info = synth.get_frequency_info()
    print("Información de frecuencias:")
    print(f"  f₀: {freq_info['f0']} Hz")
    print(f"  Armónicos: {freq_info['harmonics']}")
    print(f"  Frecuencias generadas:")
    for n, f in zip(freq_info['harmonics'], freq_info['frequencies_hz']):
        print(f"    n={n}: {f:.4f} Hz")
    print()
    
    # Patrones de resonancia
    print("Patrones de resonancia disponibles:")
    patterns = ["full", "basic", "extended", "golden"]
    for pattern in patterns:
        t_pattern, signal_pattern = synth.synthesize_resonant_pattern(0.1, pattern)
        print(f"  - {pattern}: {len(signal_pattern)} muestras")
    print()
    
    print("✓ Síntesis armónica completada exitosamente")
    print()
    print("Nota: Para guardar como audio WAV, instalar scipy:")
    print("  pip install scipy")
    print()
    print("Ejemplo de uso:")
    print("  synth.save_to_wav('resonancia_f0.wav', duration=5.0)")
    print()


if __name__ == "__main__":
    demo_harmonic_synthesis()
