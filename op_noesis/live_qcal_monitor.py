"""
Módulo de Monitoreo QCAL en Tiempo Real

Sistema para rastrear la coherencia temporal en tiempo real,
calculando la fase δ = (T / τ₀) mod 1 y proporcionando
lecturas instantáneas de la coherencia temporal global.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
License: MIT
"""

import time
import numpy as np
from typing import Optional, Dict, List, Tuple
from datetime import datetime
import warnings


# Constantes fundamentales
F0 = 141.7001  # Hz - Frecuencia de resonancia QCAL
TAU_0 = 1.0 / F0  # Período fundamental (segundos)


class QCALMonitor:
    """
    Monitor de coherencia temporal QCAL en tiempo real.
    
    Rastrea la fase temporal δ = (T / τ₀) mod 1 y proporciona
    métricas de coherencia en relación al pulso universal.
    """
    
    def __init__(
        self,
        time_source: str = "system",
        reference_timestamp: Optional[float] = None
    ):
        """
        Inicializa el monitor QCAL.
        
        Args:
            time_source: Fuente de tiempo ("system", "ntp", "utc")
            reference_timestamp: Timestamp de referencia opcional (Unix epoch)
        """
        self.f0 = F0
        self.tau_0 = TAU_0
        self.time_source = time_source
        
        # Timestamp de referencia (punto cero para cálculos de fase)
        if reference_timestamp is None:
            self.reference_timestamp = time.time()
        else:
            self.reference_timestamp = reference_timestamp
            
        # Historial de mediciones
        self.measurements: List[Dict] = []
        
        # Advertencias sobre fuentes de tiempo
        if time_source == "ntp":
            warnings.warn(
                "Fuente de tiempo NTP no implementada. "
                "Usando tiempo de sistema. "
                "Para precisión alta, implementar cliente NTP."
            )
        elif time_source == "utc":
            warnings.warn(
                "Fuente de tiempo UTC: Usando time.time() del sistema."
            )
    
    def get_current_timestamp(self) -> float:
        """
        Obtiene el timestamp actual según la fuente configurada.
        
        Returns:
            Timestamp Unix (segundos desde epoch)
        """
        if self.time_source == "system":
            return time.time()
        elif self.time_source == "ntp":
            # TODO: Implementar cliente NTP para alta precisión
            # Por ahora, usar tiempo de sistema
            return time.time()
        elif self.time_source == "utc":
            return time.time()
        else:
            return time.time()
    
    def calculate_phase(self, timestamp: Optional[float] = None) -> float:
        """
        Calcula la fase temporal δ = (T / τ₀) mod 1.
        
        Args:
            timestamp: Timestamp opcional (usa actual si None)
            
        Returns:
            Fase δ en rango [0, 1)
        """
        if timestamp is None:
            timestamp = self.get_current_timestamp()
            
        # Tiempo transcurrido desde referencia
        T = timestamp - self.reference_timestamp
        
        # Calcular fase: δ = (T / τ₀) mod 1
        delta = (T / self.tau_0) % 1.0
        
        return delta
    
    def calculate_coherence(self, delta: float) -> float:
        """
        Calcula el índice de coherencia basado en la fase.
        
        La coherencia es máxima cuando δ ≈ 0 o δ ≈ 1 (picos del ciclo)
        y mínima cuando δ ≈ 0.5 (punto medio del ciclo).
        
        Args:
            delta: Fase temporal en [0, 1)
            
        Returns:
            Índice de coherencia en [0, 1]
        """
        # Coherencia como función coseno: máxima en 0/1, mínima en 0.5
        coherence = (np.cos(2 * np.pi * delta) + 1) / 2
        return coherence
    
    def calculate_entropy(self, coherence: float) -> float:
        """
        Calcula la entropía relativa basada en la coherencia.
        
        Args:
            coherence: Índice de coherencia en [0, 1]
            
        Returns:
            Entropía relativa (valores bajos = alta coherencia)
        """
        # Entropía inversamente proporcional a coherencia
        entropy = 1.0 - coherence
        return entropy
    
    def measure(self, timestamp: Optional[float] = None) -> Dict:
        """
        Realiza una medición completa de coherencia temporal.
        
        Args:
            timestamp: Timestamp opcional (usa actual si None)
            
        Returns:
            Diccionario con métricas de coherencia
        """
        if timestamp is None:
            timestamp = self.get_current_timestamp()
            
        # Calcular fase
        delta = self.calculate_phase(timestamp)
        
        # Calcular coherencia
        coherence = self.calculate_coherence(delta)
        
        # Calcular entropía
        entropy = self.calculate_entropy(coherence)
        
        # Crear registro de medición
        measurement = {
            "timestamp": timestamp,
            "datetime": datetime.fromtimestamp(timestamp).isoformat(),
            "time_elapsed": timestamp - self.reference_timestamp,
            "phase_delta": delta,
            "coherence": coherence,
            "entropy": entropy,
            "f0": self.f0,
            "tau_0": self.tau_0,
            "is_peak": coherence > 0.9,  # Pico de coherencia
            "is_valley": coherence < 0.1  # Valle de coherencia
        }
        
        # Guardar en historial
        self.measurements.append(measurement)
        
        return measurement
    
    def monitor_continuous(
        self,
        duration: float,
        interval: float = 0.1
    ) -> List[Dict]:
        """
        Monitorea la coherencia continuamente durante un período.
        
        Args:
            duration: Duración del monitoreo en segundos
            interval: Intervalo entre mediciones en segundos
            
        Returns:
            Lista de mediciones
        """
        start_time = time.time()
        measurements = []
        
        while (time.time() - start_time) < duration:
            measurement = self.measure()
            measurements.append(measurement)
            time.sleep(interval)
            
        return measurements
    
    def get_statistics(self) -> Dict:
        """
        Calcula estadísticas del historial de mediciones.
        
        Returns:
            Diccionario con estadísticas
        """
        if not self.measurements:
            return {
                "n_measurements": 0,
                "message": "No hay mediciones disponibles"
            }
            
        phases = [m["phase_delta"] for m in self.measurements]
        coherences = [m["coherence"] for m in self.measurements]
        entropies = [m["entropy"] for m in self.measurements]
        
        return {
            "n_measurements": len(self.measurements),
            "phase": {
                "mean": np.mean(phases),
                "std": np.std(phases),
                "min": np.min(phases),
                "max": np.max(phases)
            },
            "coherence": {
                "mean": np.mean(coherences),
                "std": np.std(coherences),
                "min": np.min(coherences),
                "max": np.max(coherences)
            },
            "entropy": {
                "mean": np.mean(entropies),
                "std": np.std(entropies),
                "min": np.min(entropies),
                "max": np.max(entropies)
            },
            "peaks_detected": sum(1 for m in self.measurements if m["is_peak"]),
            "valleys_detected": sum(1 for m in self.measurements if m["is_valley"])
        }
    
    def find_coherence_windows(
        self,
        threshold: float = 0.8,
        min_duration: float = 0.01
    ) -> List[Tuple[float, float]]:
        """
        Identifica ventanas temporales de alta coherencia.
        
        Args:
            threshold: Umbral mínimo de coherencia
            min_duration: Duración mínima de ventana en segundos
            
        Returns:
            Lista de tuplas (inicio, fin) con timestamps de ventanas
        """
        if not self.measurements:
            return []
            
        windows = []
        window_start = None
        
        for i, m in enumerate(self.measurements):
            if m["coherence"] >= threshold:
                # Inicio de ventana
                if window_start is None:
                    window_start = m["timestamp"]
            else:
                # Fin de ventana
                if window_start is not None:
                    window_end = self.measurements[i-1]["timestamp"]
                    duration = window_end - window_start
                    
                    if duration >= min_duration:
                        windows.append((window_start, window_end))
                    
                    window_start = None
        
        # Cerrar última ventana si está abierta
        if window_start is not None:
            window_end = self.measurements[-1]["timestamp"]
            duration = window_end - window_start
            if duration >= min_duration:
                windows.append((window_start, window_end))
        
        return windows
    
    def reset(self, new_reference: Optional[float] = None):
        """
        Reinicia el monitor con una nueva referencia temporal.
        
        Args:
            new_reference: Nuevo timestamp de referencia (usa actual si None)
        """
        if new_reference is None:
            self.reference_timestamp = time.time()
        else:
            self.reference_timestamp = new_reference
            
        self.measurements = []


def demo_qcal_monitor():
    """
    Demostración del monitor QCAL.
    """
    print("=" * 70)
    print("Demostración del Monitor QCAL en Tiempo Real")
    print("=" * 70)
    print()
    print(f"Frecuencia f₀: {F0} Hz")
    print(f"Período τ₀: {TAU_0*1000:.6f} ms")
    print()
    
    # Crear monitor
    monitor = QCALMonitor(time_source="system")
    
    print("Iniciando mediciones en tiempo real...")
    print()
    
    # Tomar algunas mediciones
    for i in range(5):
        measurement = monitor.measure()
        
        print(f"Medición {i+1}:")
        print(f"  Timestamp: {measurement['datetime']}")
        print(f"  Fase δ: {measurement['phase_delta']:.6f}")
        print(f"  Coherencia: {measurement['coherence']:.6f}")
        print(f"  Entropía: {measurement['entropy']:.6f}")
        
        if measurement['is_peak']:
            print("  ⚡ PICO DE COHERENCIA DETECTADO")
        elif measurement['is_valley']:
            print("  ⚠ Valle de coherencia")
        
        print()
        time.sleep(0.5)
    
    # Estadísticas
    stats = monitor.get_statistics()
    print("Estadísticas del monitoreo:")
    print(f"  Total de mediciones: {stats['n_measurements']}")
    print(f"  Coherencia promedio: {stats['coherence']['mean']:.6f}")
    print(f"  Entropía promedio: {stats['entropy']['mean']:.6f}")
    print(f"  Picos detectados: {stats['peaks_detected']}")
    print(f"  Valles detectados: {stats['valleys_detected']}")
    print()
    
    # Ventanas de coherencia
    windows = monitor.find_coherence_windows(threshold=0.7)
    if windows:
        print(f"Ventanas de alta coherencia (threshold=0.7): {len(windows)}")
        for start, end in windows[:3]:  # Mostrar primeras 3
            duration_ms = (end - start) * 1000
            print(f"  - Duración: {duration_ms:.2f} ms")
    else:
        print("No se detectaron ventanas de alta coherencia")
    print()
    
    print("✓ Monitoreo QCAL completado exitosamente")
    print()
    print("Nota: Para precisión de microsegundos, implementar:")
    print("  - Cliente NTP de alta precisión")
    print("  - Sincronización con satélites GPS")
    print("  - Hardware de timestamp dedicado")
    print()


if __name__ == "__main__":
    demo_qcal_monitor()
