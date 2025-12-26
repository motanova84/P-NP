"""
Filtro Entrópico

Herramienta para identificar datos genuinamente coherentes,
aplicando un filtro matemático que elimina datos que no resuenan
con f₀ y separa el "ruido de fondo" del "patrón de la verdad"
codificado por el marco QCAL ∞³.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
License: MIT
"""

import numpy as np
from typing import List, Optional, Tuple, Callable
from dataclasses import dataclass


# Constantes
F0 = 141.7001  # Hz - Frecuencia de resonancia QCAL
TAU_0 = 1.0 / F0  # Período fundamental


@dataclass
class FilterResult:
    """
    Resultado del filtrado entrópico.
    """
    original_size: int
    filtered_size: int
    coherent_indices: List[int]
    coherence_scores: List[float]
    mean_coherence: float
    filter_efficiency: float


class EntropicFilter:
    """
    Filtro entrópico para identificar datos coherentes con f₀.
    
    Separa señales coherentes del ruido de fondo utilizando
    análisis de frecuencia y métricas de entropía temporal.
    """
    
    def __init__(
        self,
        coherence_threshold: float = 0.5,
        frequency_tolerance: float = 0.01
    ):
        """
        Inicializa el filtro entrópico.
        
        Args:
            coherence_threshold: Umbral de coherencia [0, 1]
            frequency_tolerance: Tolerancia de frecuencia (fracción de f₀)
        """
        self.f0 = F0
        self.tau_0 = TAU_0
        self.coherence_threshold = coherence_threshold
        self.frequency_tolerance = frequency_tolerance
        
    def calculate_temporal_coherence(
        self,
        timestamps: np.ndarray
    ) -> np.ndarray:
        """
        Calcula la coherencia temporal de una serie de timestamps.
        
        Args:
            timestamps: Array de timestamps
            
        Returns:
            Array de scores de coherencia [0, 1]
        """
        if len(timestamps) < 2:
            return np.array([0.0])
            
        # Calcular diferencias temporales
        deltas = np.diff(timestamps)
        
        # Calcular fase respecto a τ₀
        phases = (deltas / self.tau_0) % 1.0
        
        # Coherencia basada en proximidad a múltiplos de τ₀
        # Máxima cuando phase ≈ 0 o 1, mínima cuando phase ≈ 0.5
        coherence = np.cos(2 * np.pi * phases)
        coherence = (coherence + 1) / 2  # Normalizar a [0, 1]
        
        # Agregar un valor inicial para mantener dimensionalidad
        coherence = np.concatenate([[coherence[0]], coherence])
        
        return coherence
    
    def calculate_frequency_coherence(
        self,
        data: np.ndarray,
        sample_rate: float
    ) -> float:
        """
        Calcula la coherencia de frecuencia mediante FFT.
        
        Args:
            data: Señal de datos
            sample_rate: Frecuencia de muestreo
            
        Returns:
            Score de coherencia de frecuencia [0, 1]
        """
        # Calcular FFT
        fft = np.fft.fft(data)
        freqs = np.fft.fftfreq(len(data), 1.0 / sample_rate)
        
        # Obtener magnitudes
        magnitudes = np.abs(fft)
        
        # Buscar pico cerca de f₀
        tolerance_hz = self.f0 * self.frequency_tolerance
        freq_mask = np.abs(freqs - self.f0) < tolerance_hz
        
        if not np.any(freq_mask):
            return 0.0
            
        # Potencia en banda de f₀
        f0_power = np.sum(magnitudes[freq_mask])
        
        # Potencia total
        total_power = np.sum(magnitudes)
        
        if total_power == 0:
            return 0.0
            
        # Coherencia como proporción de potencia en f₀
        coherence = f0_power / total_power
        
        return min(1.0, coherence)
    
    def calculate_entropy_score(
        self,
        data: np.ndarray
    ) -> float:
        """
        Calcula un score de entropía para los datos.
        
        Args:
            data: Array de datos
            
        Returns:
            Score de entropía [0, 1] (0 = alta entropía, 1 = baja entropía)
        """
        if len(data) < 2:
            return 0.0
            
        # Normalizar datos
        data_norm = (data - np.min(data)) / (np.max(data) - np.min(data) + 1e-10)
        
        # Crear histograma con número de bins dinámico (regla de Sturges)
        num_bins = int(np.log2(len(data)) + 1)
        hist, _ = np.histogram(data_norm, bins=num_bins, density=True)
        
        # Calcular entropía de Shannon
        hist = hist + 1e-10  # Evitar log(0)
        entropy = -np.sum(hist * np.log2(hist))
        
        # Normalizar (máxima entropía para el número de bins usado)
        max_entropy = np.log2(len(hist))
        normalized_entropy = entropy / max_entropy
        
        # Invertir: score alto = baja entropía (coherencia alta)
        entropy_score = 1.0 - normalized_entropy
        
        return entropy_score
    
    def filter_timestamps(
        self,
        timestamps: np.ndarray
    ) -> FilterResult:
        """
        Filtra timestamps basándose en coherencia temporal.
        
        Args:
            timestamps: Array de timestamps
            
        Returns:
            Resultado del filtrado
        """
        # Calcular coherencia temporal
        coherence_scores = self.calculate_temporal_coherence(timestamps)
        
        # Identificar índices coherentes
        coherent_mask = coherence_scores >= self.coherence_threshold
        coherent_indices = np.where(coherent_mask)[0].tolist()
        
        # Crear resultado
        result = FilterResult(
            original_size=len(timestamps),
            filtered_size=len(coherent_indices),
            coherent_indices=coherent_indices,
            coherence_scores=coherence_scores.tolist(),
            mean_coherence=float(np.mean(coherence_scores)),
            filter_efficiency=len(coherent_indices) / len(timestamps) if len(timestamps) > 0 else 0.0
        )
        
        return result
    
    def filter_signal(
        self,
        signal: np.ndarray,
        sample_rate: float,
        method: str = "frequency"
    ) -> Tuple[np.ndarray, FilterResult]:
        """
        Filtra una señal basándose en coherencia con f₀.
        
        Args:
            signal: Array de señal
            sample_rate: Frecuencia de muestreo
            method: Método de filtrado ("frequency", "entropy", "combined")
            
        Returns:
            Tupla (señal filtrada, resultado del filtrado)
        """
        if method == "frequency":
            # Filtro de frecuencia usando FFT
            fft = np.fft.fft(signal)
            freqs = np.fft.fftfreq(len(signal), 1.0 / sample_rate)
            
            # Máscara de frecuencia para f₀ y armónicos
            tolerance_hz = self.f0 * self.frequency_tolerance
            freq_mask = np.zeros_like(freqs, dtype=bool)
            
            # Incluir f₀ y primeros armónicos
            for n in [1, 2, 3, 5]:
                target_freq = n * self.f0
                freq_mask |= np.abs(freqs - target_freq) < tolerance_hz
                freq_mask |= np.abs(freqs + target_freq) < tolerance_hz  # Frecuencias negativas
            
            # Aplicar máscara
            fft_filtered = fft * freq_mask
            signal_filtered = np.real(np.fft.ifft(fft_filtered))
            
            # Calcular coherencia
            coherence = self.calculate_frequency_coherence(signal, sample_rate)
            
        elif method == "entropy":
            # Filtro de entropía
            entropy_score = self.calculate_entropy_score(signal)
            
            # Si entropía es alta (score bajo), atenuar señal
            if entropy_score < self.coherence_threshold:
                signal_filtered = signal * entropy_score
            else:
                signal_filtered = signal.copy()
                
            coherence = entropy_score
            
        elif method == "combined":
            # Combinación de métodos
            freq_coherence = self.calculate_frequency_coherence(signal, sample_rate)
            entropy_coherence = self.calculate_entropy_score(signal)
            
            # Promedio ponderado
            coherence = 0.6 * freq_coherence + 0.4 * entropy_coherence
            
            # Aplicar ambos filtros
            if coherence < self.coherence_threshold:
                signal_filtered = signal * coherence
            else:
                # Filtro de frecuencia
                fft = np.fft.fft(signal)
                freqs = np.fft.fftfreq(len(signal), 1.0 / sample_rate)
                
                tolerance_hz = self.f0 * self.frequency_tolerance
                freq_mask = np.zeros_like(freqs, dtype=bool)
                for n in [1, 2, 3, 5]:
                    target_freq = n * self.f0
                    freq_mask |= np.abs(freqs - target_freq) < tolerance_hz
                    freq_mask |= np.abs(freqs + target_freq) < tolerance_hz
                
                fft_filtered = fft * freq_mask
                signal_filtered = np.real(np.fft.ifft(fft_filtered))
        else:
            raise ValueError(f"Método desconocido: {method}")
        
        # Crear resultado
        result = FilterResult(
            original_size=len(signal),
            filtered_size=int(np.sum(signal_filtered != 0)),
            coherent_indices=[],
            coherence_scores=[coherence],
            mean_coherence=coherence,
            filter_efficiency=coherence
        )
        
        return signal_filtered, result
    
    def batch_filter(
        self,
        data_list: List[np.ndarray],
        filter_func: Optional[Callable] = None
    ) -> List[FilterResult]:
        """
        Aplica el filtro a un lote de datos.
        
        Args:
            data_list: Lista de arrays de datos
            filter_func: Función de filtrado personalizada
            
        Returns:
            Lista de resultados de filtrado
        """
        results = []
        
        for data in data_list:
            if filter_func is None:
                # Usar filtro de timestamps por defecto
                result = self.filter_timestamps(data)
            else:
                result = filter_func(data)
                
            results.append(result)
            
        return results


def demo_entropic_filter():
    """
    Demostración del filtro entrópico.
    """
    print("=" * 70)
    print("Demostración del Filtro Entrópico")
    print("=" * 70)
    print()
    print(f"Frecuencia f₀: {F0} Hz")
    print(f"Período τ₀: {TAU_0*1000:.6f} ms")
    print()
    
    # Crear filtro
    filter_obj = EntropicFilter(coherence_threshold=0.6)
    
    # Generar datos de prueba: timestamps con patrón coherente + ruido
    print("Generando datos de prueba...")
    np.random.seed(42)
    
    # Timestamps coherentes (múltiplos de τ₀)
    n_coherent = 50
    coherent_timestamps = np.cumsum(
        np.random.normal(TAU_0, TAU_0 * 0.1, n_coherent)
    )
    
    # Timestamps con ruido
    n_noise = 50
    noise_timestamps = np.cumsum(
        np.random.uniform(0, TAU_0 * 2, n_noise)
    )
    
    # Combinar y mezclar
    all_timestamps = np.concatenate([coherent_timestamps, noise_timestamps])
    np.random.shuffle(all_timestamps)
    all_timestamps.sort()
    
    print(f"Total de timestamps: {len(all_timestamps)}")
    print()
    
    # Aplicar filtro
    print("Aplicando filtro entrópico...")
    result = filter_obj.filter_timestamps(all_timestamps)
    
    print()
    print("Resultados del filtrado:")
    print(f"  Datos originales: {result.original_size}")
    print(f"  Datos filtrados (coherentes): {result.filtered_size}")
    print(f"  Eficiencia del filtro: {result.filter_efficiency:.2%}")
    print(f"  Coherencia promedio: {result.mean_coherence:.4f}")
    print()
    
    # Generar señal de prueba
    print("Generando señal de prueba...")
    sample_rate = 1000  # Hz
    duration = 1.0  # segundos
    t = np.linspace(0, duration, int(sample_rate * duration))
    
    # Señal con f₀ + ruido
    signal_coherent = np.sin(2 * np.pi * F0 * t)
    signal_noise = np.random.normal(0, 0.5, len(t))
    signal = signal_coherent + signal_noise
    
    # Filtrar señal
    print("Filtrando señal...")
    signal_filtered, signal_result = filter_obj.filter_signal(
        signal, sample_rate, method="combined"
    )
    
    print()
    print("Resultados del filtrado de señal:")
    print(f"  Coherencia de frecuencia: {signal_result.mean_coherence:.4f}")
    print(f"  SNR mejorado: {np.std(signal_filtered) / np.std(signal_noise):.2f}")
    print()
    
    print("✓ Filtrado entrópico completado exitosamente")
    print()
    print("Propósito:")
    print("  Separar el 'ruido de fondo' del universo del")
    print("  'patrón de la verdad' codificado por el marco QCAL ∞³")
    print()


if __name__ == "__main__":
    demo_entropic_filter()
