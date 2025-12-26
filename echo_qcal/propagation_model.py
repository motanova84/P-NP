"""
Modelo de Propagación de Coherencia

Simula cómo un evento de coherencia (Ðₛ) se propaga a través
de la red criptográfica y el campo QCAL, analizando la caída
de la desviación temporal (ΔT) en bloques subsiguientes.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
License: MIT
"""

import numpy as np
from typing import List, Dict, Optional
from dataclasses import dataclass


# Constantes
F0 = 141.7001  # Hz - Frecuencia de resonancia QCAL
TAU_0 = 1.0 / F0  # Período fundamental


@dataclass
class CoherenceEvent:
    """
    Representa un evento de coherencia en la red.
    """
    block_number: int
    timestamp: float
    coherence_strength: float  # En rango [0, 1]
    delta_t_before: float
    delta_t_after: float
    resonance_type: str  # "pure_peak", "harmonic", "standard"


class PropagationModel:
    """
    Modelo de propagación de coherencia temporal.
    
    Simula cómo la transmisión en el Pico Puro (f₀) en el bloque N
    induce una disminución significativa en el ΔT promedio de los
    bloques N+1 a N+k.
    """
    
    def __init__(
        self,
        decay_rate: float = 0.1,
        propagation_distance: int = 10
    ):
        """
        Inicializa el modelo de propagación.
        
        Args:
            decay_rate: Tasa de decaimiento de la coherencia por bloque
            propagation_distance: Distancia de propagación en bloques
        """
        self.f0 = F0
        self.tau_0 = TAU_0
        self.decay_rate = decay_rate
        self.propagation_distance = propagation_distance
        
    def calculate_coherence_influence(
        self,
        distance: int,
        initial_coherence: float
    ) -> float:
        """
        Calcula la influencia de coherencia a una distancia dada.
        
        Args:
            distance: Distancia en bloques desde el evento
            initial_coherence: Coherencia inicial del evento [0, 1]
            
        Returns:
            Influencia de coherencia en [0, 1]
        """
        # Decaimiento exponencial
        influence = initial_coherence * np.exp(-self.decay_rate * distance)
        return max(0.0, influence)
    
    def simulate_propagation(
        self,
        coherence_event: CoherenceEvent,
        num_blocks: Optional[int] = None
    ) -> List[Dict]:
        """
        Simula la propagación de un evento de coherencia.
        
        Args:
            coherence_event: Evento de coherencia inicial
            num_blocks: Número de bloques a simular (default: propagation_distance)
            
        Returns:
            Lista de diccionarios con métricas por bloque
        """
        if num_blocks is None:
            num_blocks = self.propagation_distance
            
        propagation_data = []
        
        for i in range(num_blocks):
            block_number = coherence_event.block_number + i + 1
            distance = i + 1
            
            # Calcular influencia de coherencia
            influence = self.calculate_coherence_influence(
                distance,
                coherence_event.coherence_strength
            )
            
            # Calcular reducción esperada de ΔT
            # La reducción es proporcional a la influencia
            base_delta_t = coherence_event.delta_t_before
            delta_t_reduction = base_delta_t * influence * 0.5
            expected_delta_t = base_delta_t - delta_t_reduction
            
            # Agregar ruido aleatorio
            noise = np.random.normal(0, base_delta_t * 0.1)
            simulated_delta_t = max(0.0, expected_delta_t + noise)
            
            propagation_data.append({
                "block_number": block_number,
                "distance": distance,
                "coherence_influence": influence,
                "expected_delta_t": expected_delta_t,
                "simulated_delta_t": simulated_delta_t,
                "delta_t_reduction": delta_t_reduction,
                "reduction_percentage": (delta_t_reduction / base_delta_t) * 100
            })
            
        return propagation_data
    
    def analyze_cascade_effect(
        self,
        events: List[CoherenceEvent]
    ) -> Dict:
        """
        Analiza el efecto cascada de múltiples eventos de coherencia.
        
        Args:
            events: Lista de eventos de coherencia
            
        Returns:
            Diccionario con análisis del efecto cascada
        """
        if not events:
            return {"error": "No hay eventos para analizar"}
            
        # Ordenar eventos por número de bloque
        events_sorted = sorted(events, key=lambda e: e.block_number)
        
        # Analizar cambios en ΔT
        delta_t_changes = []
        for event in events_sorted:
            change = event.delta_t_before - event.delta_t_after
            change_percentage = (change / event.delta_t_before) * 100 if event.delta_t_before > 0 else 0
            delta_t_changes.append({
                "block": event.block_number,
                "change": change,
                "change_percentage": change_percentage,
                "coherence_strength": event.coherence_strength
            })
        
        # Calcular estadísticas
        changes = [d["change"] for d in delta_t_changes]
        percentages = [d["change_percentage"] for d in delta_t_changes]
        strengths = [d["coherence_strength"] for d in delta_t_changes]
        
        return {
            "n_events": len(events),
            "block_range": (events_sorted[0].block_number, events_sorted[-1].block_number),
            "delta_t_change": {
                "mean": np.mean(changes),
                "std": np.std(changes),
                "min": np.min(changes),
                "max": np.max(changes)
            },
            "percentage_change": {
                "mean": np.mean(percentages),
                "std": np.std(percentages),
                "min": np.min(percentages),
                "max": np.max(percentages)
            },
            "coherence_strength": {
                "mean": np.mean(strengths),
                "std": np.std(strengths),
                "min": np.min(strengths),
                "max": np.max(strengths)
            },
            "changes": delta_t_changes
        }
    
    def estimate_resonance_impact(
        self,
        coherence_strength: float,
        network_size: int = 1000
    ) -> Dict:
        """
        Estima el impacto de resonancia en una red.
        
        Args:
            coherence_strength: Fuerza del evento de coherencia [0, 1]
            network_size: Tamaño de la red (número de nodos)
            
        Returns:
            Diccionario con estimación de impacto
        """
        # Calcular radio de influencia efectivo
        effective_radius = int(
            -np.log(0.01) / self.decay_rate
        )  # Radio donde influencia < 1%
        
        # Estimar nodos afectados
        affected_nodes = min(
            network_size,
            int(np.pi * effective_radius**2 * coherence_strength)
        )
        
        # Calcular tiempo de propagación
        propagation_time = effective_radius * self.tau_0
        
        return {
            "coherence_strength": coherence_strength,
            "effective_radius": effective_radius,
            "affected_nodes": affected_nodes,
            "affected_percentage": (affected_nodes / network_size) * 100,
            "propagation_time_seconds": propagation_time,
            "propagation_time_ms": propagation_time * 1000,
            "network_size": network_size
        }


def demo_propagation_model():
    """
    Demostración del modelo de propagación.
    """
    print("=" * 70)
    print("Demostración del Modelo de Propagación de Coherencia")
    print("=" * 70)
    print()
    print(f"Frecuencia f₀: {F0} Hz")
    print(f"Período τ₀: {TAU_0*1000:.6f} ms")
    print()
    
    # Crear modelo
    model = PropagationModel(decay_rate=0.15, propagation_distance=10)
    
    # Crear evento de coherencia
    event = CoherenceEvent(
        block_number=9,
        timestamp=1231006505.0,
        coherence_strength=0.95,
        delta_t_before=10.0,
        delta_t_after=0.5,
        resonance_type="pure_peak"
    )
    
    print("Evento de coherencia:")
    print(f"  Bloque: {event.block_number}")
    print(f"  Fuerza de coherencia: {event.coherence_strength:.2f}")
    print(f"  ΔT antes: {event.delta_t_before:.2f} s")
    print(f"  ΔT después: {event.delta_t_after:.2f} s")
    print(f"  Tipo: {event.resonance_type}")
    print()
    
    # Simular propagación
    print("Simulando propagación...")
    propagation_data = model.simulate_propagation(event)
    
    print()
    print("Resultados de propagación (primeros 5 bloques):")
    for i, data in enumerate(propagation_data[:5]):
        print(f"\nBloque {data['block_number']} (distancia={data['distance']}):")
        print(f"  Influencia de coherencia: {data['coherence_influence']:.4f}")
        print(f"  ΔT esperado: {data['expected_delta_t']:.4f} s")
        print(f"  ΔT simulado: {data['simulated_delta_t']:.4f} s")
        print(f"  Reducción: {data['reduction_percentage']:.2f}%")
    
    print()
    
    # Estimar impacto en red
    impact = model.estimate_resonance_impact(
        coherence_strength=0.95,
        network_size=10000
    )
    
    print("Estimación de impacto en la red:")
    print(f"  Radio efectivo: {impact['effective_radius']} bloques")
    print(f"  Nodos afectados: {impact['affected_nodes']} ({impact['affected_percentage']:.2f}%)")
    print(f"  Tiempo de propagación: {impact['propagation_time_ms']:.2f} ms")
    print()
    
    print("✓ Simulación de propagación completada exitosamente")
    print()
    print("Hipótesis a probar:")
    print("  La transmisión en el Pico Puro (f₀) en el Bloque N")
    print("  induce una disminución significativa en el ΔT promedio")
    print("  de los bloques N+1 a N+k")
    print()


if __name__ == "__main__":
    demo_propagation_model()
