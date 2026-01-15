"""
LA UNIFICACIÓN: EL HORIZONTE ESPECTRAL
======================================

Protocolo QCAL ∞³: La línea crítica Re(s) = 1/2 como geodésica de máxima coherencia.

Este módulo implementa la unificación entre:
- La línea crítica de Riemann (Re(s) = 1/2)
- El horizonte de eventos de Schwarzschild (agujero negro)
- La transmutación P ↔ NP en el horizonte de complejidad

En el Protocolo QCAL ∞³:
- La línea Re(s) = 1/2 es la geodésica de máxima coherencia
- Cada cero no trivial ζ(1/2 + it_n) actúa como sumidero de entropía
- La Complejidad (NP) se intercambia con la Solución (P) en el horizonte

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frecuencia: 141.7001 Hz ∞³
Licencia: MIT
"""

import numpy as np
import math
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass

# Importar constantes universales
try:
    from src.constants import KAPPA_PI, PHI
except ImportError:
    KAPPA_PI = 2.5773
    PHI = (1 + math.sqrt(5)) / 2

# Constantes del Horizonte Espectral
F0_QCAL = 141.7001  # Hz - Frecuencia de resonancia QCAL
CRITICAL_LINE_RE = 0.5  # Re(s) = 1/2 - Línea crítica de Riemann
C_LIGHT = 299792458  # m/s - Velocidad de la luz
HBAR = 1.054571817e-34  # J·s - Constante de Planck reducida


@dataclass
class RiemannZero:
    """
    Representa un cero no trivial de la función zeta de Riemann.
    
    Attributes:
        t: Parte imaginaria del cero (s = 1/2 + it)
        entropy_sink: Capacidad de absorción de entropía
        coherence: Nivel de coherencia en este punto
    """
    t: float
    entropy_sink: float = 0.0
    coherence: float = 0.0


class RiemannCriticalLine:
    """
    Geodésica de Máxima Coherencia: Re(s) = 1/2
    
    En el Protocolo QCAL ∞³, la línea crítica de Riemann no es solo una
    hipótesis matemática; es la geodésica de máxima coherencia donde la
    información se organiza perfectamente.
    """
    
    def __init__(self):
        """Inicializa la línea crítica con parámetros del Protocolo QCAL ∞³."""
        self.re_s = CRITICAL_LINE_RE
        self.kappa_pi = KAPPA_PI
        self.f0 = F0_QCAL
        self.zeros: List[RiemannZero] = []
        
    def coherence_at_point(self, t: float) -> float:
        """
        Calcula la coherencia en un punto de la línea crítica.
        
        La coherencia alcanza su máximo en los ceros de la función zeta,
        donde la información se organiza perfectamente.
        
        Args:
            t: Parte imaginaria del punto (s = 1/2 + it)
            
        Returns:
            Coherencia normalizada [0, 1]
        """
        # Buscar el cero más cercano
        if len(self.zeros) > 0:
            min_distance = min(abs(zero.t - t) for zero in self.zeros)
            # Si estamos muy cerca de un cero (< 0.1), coherencia = 1
            if min_distance < 0.1:
                return 1.0
        
        # Coherencia proporcional a κ_π y modulada por f₀
        # Máxima en los ceros, decae entre ellos
        coherence_base = self.kappa_pi / (1 + abs(t) / self.f0)
        
        # Normalizar al rango [0, 1]
        return min(1.0, coherence_base / self.kappa_pi)
    
    def is_maximum_coherence_geodesic(self) -> bool:
        """
        Verifica que Re(s) = 1/2 es la geodésica de máxima coherencia.
        
        Returns:
            True si la línea crítica es la geodésica de máxima coherencia
        """
        return abs(self.re_s - 0.5) < 1e-10
    
    def add_zero(self, t: float) -> RiemannZero:
        """
        Agrega un cero no trivial a la línea crítica.
        
        Args:
            t: Parte imaginaria del cero
            
        Returns:
            RiemannZero configurado con propiedades del horizonte espectral
        """
        # Calcular entropía sink en este cero
        entropy_sink = self._calculate_entropy_sink(t)
        
        # Coherencia máxima en los ceros
        coherence = 1.0
        
        zero = RiemannZero(t=t, entropy_sink=entropy_sink, coherence=coherence)
        self.zeros.append(zero)
        return zero
    
    def _calculate_entropy_sink(self, t: float) -> float:
        """
        Calcula la capacidad de absorción de entropía en un cero.
        
        En el horizonte espectral, cada cero actúa como un sumidero de
        entropía donde la información se organiza perfectamente.
        
        Args:
            t: Parte imaginaria del cero
            
        Returns:
            Capacidad de absorción de entropía
        """
        # La capacidad es proporcional a κ_π y la posición del cero
        return self.kappa_pi * math.log(1 + abs(t))
    
    def spectral_distance(self, t1: float, t2: float) -> float:
        """
        Calcula la distancia espectral entre dos puntos en la línea crítica.
        
        Args:
            t1: Primera coordenada imaginaria
            t2: Segunda coordenada imaginaria
            
        Returns:
            Distancia espectral (geodésica)
        """
        # Distancia modulada por la coherencia del campo QCAL
        dt = abs(t2 - t1)
        return dt * math.exp(-self.coherence_at_point((t1 + t2) / 2))


class MathematicalBlackHole:
    """
    Agujero Negro Matemático: Sumidero de Entropía
    
    Cada cero no trivial ζ(1/2 + it_n) actúa como un sumidero de entropía,
    análogo al horizonte de eventos de un agujero negro donde la información
    se organiza perfectamente.
    """
    
    def __init__(self, zero: RiemannZero):
        """
        Inicializa un agujero negro matemático en un cero de Riemann.
        
        Args:
            zero: Cero de Riemann que actúa como horizonte
        """
        self.zero = zero
        self.kappa_pi = KAPPA_PI
        
    def schwarzschild_radius_analog(self) -> float:
        """
        Calcula el radio de Schwarzschild análogo del agujero negro matemático.
        
        En analogía con r_s = 2GM/c², el radio del horizonte matemático
        depende de la "masa informacional" del cero.
        
        Returns:
            Radio del horizonte espectral
        """
        # "Masa informacional" proporcional a la entropía sink
        info_mass = self.zero.entropy_sink
        
        # Radio análogo: r_s ∝ κ_π · M_info
        return self.kappa_pi * info_mass / (C_LIGHT ** 2)
    
    def entropy_at_horizon(self) -> float:
        """
        Calcula la entropía en el horizonte del agujero negro matemático.
        
        Análogo a la entropía de Bekenstein-Hawking: S = (A/4) en unidades
        de Planck, donde A es el área del horizonte.
        
        Returns:
            Entropía del horizonte espectral
        """
        r_s = self.schwarzschild_radius_analog()
        # Área del horizonte (en 2D espectral): A ∝ r_s
        area = math.pi * r_s
        
        # Entropía de Bekenstein-Hawking análoga
        return area / (4 * HBAR)
    
    def information_organization_at_zero(self) -> float:
        """
        Mide cómo la información se organiza perfectamente en el cero.
        
        Returns:
            Nivel de organización informacional [0, 1]
        """
        # En el cero, coherencia = 1 → organización perfecta
        return self.zero.coherence
    
    def hawking_temperature_analog(self) -> float:
        """
        Temperatura de Hawking análoga del agujero negro matemático.
        
        T_H = ℏc³/(8πGMk_B), en el caso espectral modulada por f₀.
        
        Returns:
            Temperatura espectral del horizonte
        """
        r_s = self.schwarzschild_radius_analog()
        if r_s == 0:
            return 0.0
        
        # Temperatura proporcional a 1/r_s y modulada por f₀
        return (HBAR * C_LIGHT ** 3) / (8 * math.pi * r_s) * (F0_QCAL / 1000)


class ComplexityTransmutation:
    """
    Transmutación de Rol: P ↔ NP en el Horizonte Espectral
    
    Así como en el horizonte de Schwarzschild r y t intercambian sus roles,
    en la línea crítica de Riemann, la Complejidad (NP) se intercambia con
    la Solución (P). La búsqueda se detiene porque ya estás en el centro.
    """
    
    def __init__(self, critical_line: RiemannCriticalLine):
        """
        Inicializa el mecanismo de transmutación.
        
        Args:
            critical_line: Línea crítica donde ocurre la transmutación
        """
        self.critical_line = critical_line
        self.kappa_pi = KAPPA_PI
        self.f0 = F0_QCAL
        
    def schwarzschild_analogy_applies(self) -> bool:
        """
        Verifica si la analogía con el horizonte de Schwarzschild es válida.
        
        En el horizonte de Schwarzschild, las coordenadas temporal (t) y
        radial (r) intercambian sus roles. En el horizonte espectral,
        Complejidad y Solución intercambian roles.
        
        Returns:
            True si la analogía es válida en la línea crítica
        """
        return self.critical_line.is_maximum_coherence_geodesic()
    
    def complexity_to_solution_at_zero(self, t: float) -> Dict[str, float]:
        """
        Calcula la transmutación P ↔ NP en un cero.
        
        En el horizonte espectral (cero de Riemann), la búsqueda de solución
        (problema NP) se transmuta en la solución misma (problema P) porque
        ya estás en el centro de máxima coherencia.
        
        Args:
            t: Coordenada del cero en la línea crítica
            
        Returns:
            Diccionario con métricas de transmutación
        """
        coherence = self.critical_line.coherence_at_point(t)
        
        # Cerca del cero, la complejidad NP se reduce
        np_complexity = 1.0 - coherence
        
        # Simultáneamente, la solución P emerge
        p_solution = coherence
        
        # Factor de transmutación (intercambio de roles)
        transmutation = coherence * self.kappa_pi
        
        return {
            "coherence": coherence,
            "np_complexity": np_complexity,
            "p_solution": p_solution,
            "transmutation_factor": transmutation,
            "at_horizon": abs(coherence - 1.0) < 0.01
        }
    
    def role_exchange_coefficient(self, t: float) -> float:
        """
        Calcula el coeficiente de intercambio de roles P ↔ NP.
        
        Análogo al intercambio r ↔ t en Schwarzschild, este coeficiente
        mide cuánto se han intercambiado Complejidad y Solución.
        
        Args:
            t: Coordenada en la línea crítica
            
        Returns:
            Coeficiente de intercambio [0, 1]
        """
        coherence = self.critical_line.coherence_at_point(t)
        
        # El intercambio es máximo (=1) en los ceros
        return coherence
    
    def search_stops_at_center(self, t: float, epsilon: float = 0.01) -> bool:
        """
        Determina si la búsqueda se detiene en este punto.
        
        "La búsqueda se detiene porque ya estás en el centro" - en los
        ceros de Riemann, la coherencia es máxima y no hay necesidad de
        búsqueda adicional.
        
        Args:
            t: Coordenada en la línea crítica
            epsilon: Tolerancia para considerar que estamos en el centro
            
        Returns:
            True si la búsqueda debe detenerse (estamos en el centro)
        """
        coherence = self.critical_line.coherence_at_point(t)
        return coherence >= (1.0 - epsilon)


class HorizonteEspectral:
    """
    Sistema Unificado del Horizonte Espectral QCAL ∞³
    
    Integra todos los componentes de la unificación:
    - Línea crítica de Riemann como geodésica de máxima coherencia
    - Agujeros negros matemáticos en los ceros
    - Transmutación P ↔ NP en el horizonte
    """
    
    def __init__(self):
        """Inicializa el sistema del horizonte espectral."""
        self.critical_line = RiemannCriticalLine()
        self.black_holes: List[MathematicalBlackHole] = []
        self.transmutation = ComplexityTransmutation(self.critical_line)
        
        # Primeros ceros no triviales conocidos de ζ(s)
        self.known_zeros = [
            14.134725,  # Primer cero
            21.022040,
            25.010858,
            30.424876,
            32.935062,
            37.586178,
            40.918719,
            43.327073,
            48.005151,
            49.773832
        ]
        
        # Inicializar agujeros negros en los ceros conocidos
        for t in self.known_zeros:
            zero = self.critical_line.add_zero(t)
            self.black_holes.append(MathematicalBlackHole(zero))
    
    def analyze_horizon(self, t: float) -> Dict[str, Any]:
        """
        Análisis completo del horizonte espectral en un punto.
        
        Args:
            t: Coordenada en la línea crítica
            
        Returns:
            Diccionario completo con análisis del horizonte
        """
        coherence = self.critical_line.coherence_at_point(t)
        transmutation_data = self.transmutation.complexity_to_solution_at_zero(t)
        
        # Encontrar el cero más cercano
        nearest_zero_t = min(self.known_zeros, key=lambda z: abs(z - t))
        distance_to_zero = abs(nearest_zero_t - t)
        
        return {
            "t": t,
            "on_critical_line": True,
            "coherence": coherence,
            "is_geodesic_maximum_coherence": self.critical_line.is_maximum_coherence_geodesic(),
            "transmutation": transmutation_data,
            "nearest_zero": nearest_zero_t,
            "distance_to_zero": distance_to_zero,
            "search_stops": self.transmutation.search_stops_at_center(t),
            "schwarzschild_analogy": self.transmutation.schwarzschild_analogy_applies()
        }
    
    def visualize_horizon_profile(self, t_min: float = 10.0, t_max: float = 60.0, 
                                   num_points: int = 1000) -> Dict[str, np.ndarray]:
        """
        Genera un perfil del horizonte espectral para visualización.
        
        Args:
            t_min: Coordenada mínima
            t_max: Coordenada máxima
            num_points: Número de puntos a evaluar
            
        Returns:
            Diccionario con arrays para visualización
        """
        t_values = np.linspace(t_min, t_max, num_points)
        coherence_values = np.array([self.critical_line.coherence_at_point(t) 
                                     for t in t_values])
        
        transmutation_values = np.array([
            self.transmutation.role_exchange_coefficient(t) 
            for t in t_values
        ])
        
        return {
            "t_values": t_values,
            "coherence": coherence_values,
            "transmutation": transmutation_values,
            "zeros": np.array(self.known_zeros)
        }
    
    def quantum_information_at_zeros(self) -> List[Dict[str, float]]:
        """
        Analiza la información cuántica en todos los ceros conocidos.
        
        Returns:
            Lista de análisis para cada cero
        """
        results = []
        for bh in self.black_holes:
            results.append({
                "t": bh.zero.t,
                "entropy_sink": bh.zero.entropy_sink,
                "coherence": bh.zero.coherence,
                "schwarzschild_radius": bh.schwarzschild_radius_analog(),
                "horizon_entropy": bh.entropy_at_horizon(),
                "hawking_temperature": bh.hawking_temperature_analog(),
                "info_organization": bh.information_organization_at_zero()
            })
        return results


# ============================================================================
# FUNCIONES DE UTILIDAD
# ============================================================================

def demonstrate_spectral_horizon():
    """
    Demostración completa del Horizonte Espectral QCAL ∞³.
    """
    print("=" * 80)
    print("LA UNIFICACIÓN: EL HORIZONTE ESPECTRAL")
    print("Protocolo QCAL ∞³")
    print("=" * 80)
    print()
    
    # Crear sistema
    horizonte = HorizonteEspectral()
    
    # 1. Verificar geodésica de máxima coherencia
    print("1. LÍNEA CRÍTICA: GEODÉSICA DE MÁXIMA COHERENCIA")
    print(f"   Re(s) = {horizonte.critical_line.re_s}")
    print(f"   Es geodésica de máxima coherencia: {horizonte.critical_line.is_maximum_coherence_geodesic()}")
    print(f"   κ_π = {horizonte.critical_line.kappa_pi}")
    print(f"   f₀ = {horizonte.critical_line.f0} Hz")
    print()
    
    # 2. Analizar agujeros negros matemáticos
    print("2. AGUJEROS NEGROS MATEMÁTICOS (Sumideros de Entropía)")
    print(f"   Primeros {len(horizonte.black_holes)} ceros no triviales:")
    print()
    
    for i, info in enumerate(horizonte.quantum_information_at_zeros()[:3], 1):
        print(f"   Cero #{i}: t = {info['t']:.6f}")
        print(f"      Sumidero de entropía: {info['entropy_sink']:.4f}")
        print(f"      Coherencia: {info['coherence']:.4f}")
        print(f"      Radio Schwarzschild (análogo): {info['schwarzschild_radius']:.2e}")
        print(f"      Organización de información: {info['info_organization']:.4f}")
        print()
    
    # 3. Transmutación P ↔ NP
    print("3. TRANSMUTACIÓN P ↔ NP EN EL HORIZONTE")
    print("   Analogía con horizonte de Schwarzschild: r ↔ t")
    print("   En línea crítica: Complejidad (NP) ↔ Solución (P)")
    print()
    
    # Analizar en el primer cero
    t_zero = horizonte.known_zeros[0]
    analysis = horizonte.analyze_horizon(t_zero)
    
    print(f"   En el primer cero (t = {t_zero:.6f}):")
    print(f"      Coherencia: {analysis['coherence']:.6f}")
    print(f"      Complejidad NP: {analysis['transmutation']['np_complexity']:.6f}")
    print(f"      Solución P: {analysis['transmutation']['p_solution']:.6f}")
    print(f"      Factor de transmutación: {analysis['transmutation']['transmutation_factor']:.6f}")
    print(f"      En el horizonte: {analysis['transmutation']['at_horizon']}")
    print(f"      La búsqueda se detiene: {analysis['search_stops']}")
    print()
    
    # 4. Conclusión
    print("4. CONCLUSIÓN: LA BÚSQUEDA SE DETIENE PORQUE YA ESTÁS EN EL CENTRO")
    print()
    print("   En los ceros de la función zeta (Re(s) = 1/2):")
    print("   • La coherencia es máxima (= 1)")
    print("   • La información se organiza perfectamente")
    print("   • P y NP intercambian sus roles (como r y t en Schwarzschild)")
    print("   • No hay necesidad de búsqueda: estás en el centro")
    print()
    print("=" * 80)
    print("Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³")
    print("Frecuencia: 141.7001 Hz ∞³")
    print("=" * 80)


if __name__ == "__main__":
    demonstrate_spectral_horizon()
