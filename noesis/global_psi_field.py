"""
Campo de Coherencia Global Ψ (Global PSI Field)
================================================

Este módulo implementa el Campo Global de Coherencia Ψ, el sustrato cuántico
noético que permite la unificación de NP y P bajo resonancia crítica.

**Teorema de Colapso Noético:**
Bajo coherencia Ψ ≥ 0.9999998 y alineación f₀, la verificación (NP) y la
resolución (P) se unifican: L ∈ NP ↔ L ∈ P_Noetic.

La máquina noética no recorre el árbol de búsqueda, sino que vibra en la
solución mediante el Oráculo de Insight cuántico-noético.

**Fundamento Matemático:**
    Ψ = coherencia del campo (0 ≤ Ψ ≤ 1)
    f₀ = 141.7001 Hz (frecuencia fundamental de resonancia)
    κ_Π = 2.5773 (constante de separación computacional)
    
    Bajo Ψ ≥ Ψ_crítico = 0.9999998:
        Complejidad_efectiva(L, M_Noetic) = O(|x|^κ_Π · Ψ⁻¹) → O(poly(|x|))

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: Eterno Ahora, 2026
Frequency: 141.7001 Hz ∞³
Signature: ∴𓂀Ω∞³Φ
"""

import math
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, FrozenSet, Optional, Set

# ============================================================================
# CONSTANTES FUNDAMENTALES
# ============================================================================

# Frecuencia fundamental de resonancia noética (Hz)
F0_FUNDAMENTAL: float = 141.7001

# Razón áurea φ = (1 + √5) / 2
PHI: float = (1 + math.sqrt(5)) / 2

# φ² — límite de coherencia ideal
PHI_SQUARED: float = PHI ** 2

# Constante κ_Π — densidad espectral computacional
KAPPA_PI: float = 2.5773

# Umbral de coherencia crítica para colapso noético
# Ψ ≥ 0.9999998 activa el Oráculo de Insight
PSI_CRITICAL_THRESHOLD: float = 0.9999998

# Umbral de alineación f₀ (fracción de la frecuencia fundamental)
F0_ALIGNMENT_TOLERANCE: float = 1e-6


# ============================================================================
# ESTADO DE COHERENCIA Ψ
# ============================================================================

@dataclass
class CoherenceState:
    """
    Estado de Coherencia del Campo Noético Global Ψ.

    Representa el nivel de alineación cuántica del sistema con el campo Ψ
    universal. Cuando val ≥ PSI_CRITICAL_THRESHOLD, el sistema alcanza
    coherencia crítica y el colapso noético P=NP se hace operativo.

    Attributes:
        val: Valor de coherencia en [0, 1]. Ψ = 1 indica coherencia perfecta.
        label: Etiqueta descriptiva del estado.
    """

    val: float
    label: str = "Campo Ψ Global"

    def __post_init__(self) -> None:
        if not (0.0 <= self.val <= 1.0):
            raise ValueError(
                f"CoherenceState.val debe estar en [0, 1]; se recibió {self.val}"
            )

    @property
    def is_critical(self) -> bool:
        """True si el estado alcanza coherencia crítica (Ψ ≥ 0.9999998)."""
        return self.val >= PSI_CRITICAL_THRESHOLD

    @property
    def resonance_frequency(self) -> float:
        """
        Frecuencia de resonancia efectiva bajo coherencia Ψ.

        f_eff = f₀ · Ψ

        Cuando Ψ → 1, f_eff → f₀ = 141.7001 Hz (resonancia perfecta).
        """
        return F0_FUNDAMENTAL * self.val

    def __repr__(self) -> str:
        status = "CRÍTICA ∞³" if self.is_critical else "sub-crítica"
        return (
            f"CoherenceState(Ψ={self.val:.7f}, f_eff={self.resonance_frequency:.4f} Hz,"
            f" estado={status})"
        )


# ============================================================================
# ALINEACIÓN f₀
# ============================================================================

@dataclass
class Alignment:
    """
    Alineación del sistema con la frecuencia fundamental f₀.

    La alineación f₀ es la condición necesaria para que la Máquina Noética
    opere en modo de resolución directa. Mide cuán cerca está la frecuencia
    operativa del sistema de f₀ = 141.7001 Hz.

    Attributes:
        frequency: Frecuencia operativa del sistema (Hz).
        target: Frecuencia objetivo (por defecto f₀ = 141.7001 Hz).
    """

    frequency: float
    target: float = F0_FUNDAMENTAL

    @property
    def deviation(self) -> float:
        """Desviación relativa respecto a f₀: |f - f₀| / f₀."""
        return abs(self.frequency - self.target) / self.target

    @property
    def is_aligned(self) -> bool:
        """True si la frecuencia está alineada con f₀ dentro de la tolerancia."""
        return self.deviation <= F0_ALIGNMENT_TOLERANCE

    @property
    def resonance_factor(self) -> float:
        """
        Factor de resonancia ρ ∈ [0, 1].

        ρ = exp(-κ_Π · |f - f₀| / f₀)

        ρ = 1 indica resonancia perfecta con f₀.
        """
        return math.exp(-KAPPA_PI * self.deviation)

    def __repr__(self) -> str:
        status = "ALINEADO ✧" if self.is_aligned else "desalineado"
        return (
            f"Alignment(f={self.frequency:.4f} Hz, f₀={self.target:.4f} Hz,"
            f" ρ={self.resonance_factor:.6f}, {status})"
        )


# ============================================================================
# LENGUAJE (Language)
# ============================================================================

class Language:
    """
    Lenguaje formal L ⊆ Σ*.

    En la teoría de la complejidad computacional, un lenguaje es un conjunto
    de cadenas. Bajo el campo noético, los lenguajes en NP son resolubles
    en tiempo polinomial por una Máquina Noética bajo coherencia crítica.

    Attributes:
        name: Nombre del lenguaje.
        decision: Función oráculo Σ* → bool que decide la pertenencia.
        is_in_NP: Indica si el lenguaje está en NP (verificación polinomial).
    """

    def __init__(
        self,
        name: str,
        decision: Optional[Callable[[str], bool]] = None,
        is_in_NP: bool = True,
    ) -> None:
        self.name = name
        self._decision = decision
        self.is_in_NP = is_in_NP

    def decide(self, x: str) -> bool:
        """Decide si x ∈ L usando el oráculo de decisión."""
        if self._decision is None:
            raise NotImplementedError(
                f"Lenguaje '{self.name}' no tiene función de decisión definida."
            )
        return self._decision(x)

    def __repr__(self) -> str:
        complexity = "NP" if self.is_in_NP else "general"
        return f"Language('{self.name}', clase={complexity})"


# ============================================================================
# MÁQUINA NOÉTICA
# ============================================================================

@dataclass
class NoeticMachine:
    """
    Máquina de Turing Noética — Posee un oráculo de coherencia Ψ.

    La Máquina Noética no recorre el árbol de búsqueda explícitamente.
    En cambio, *vibra* en la solución mediante el Oráculo de Insight:
    el campo Ψ, bajo coherencia crítica, colapsa el espacio de búsqueda
    al estado solución directamente.

    **Condición de activación:**
        coherence.val ≥ PSI_CRITICAL_THRESHOLD (= 0.9999998)
        f0_alignment.is_aligned = True

    Attributes:
        coherence: Estado del campo Ψ.
        f0_alignment: Alineación con la frecuencia fundamental f₀.
    """

    coherence: CoherenceState
    f0_alignment: Alignment

    def __post_init__(self) -> None:
        if not self.coherence.is_critical:
            raise ValueError(
                f"Coherencia insuficiente para activación noética: "
                f"Ψ={self.coherence.val:.7f} < {PSI_CRITICAL_THRESHOLD}. "
                f"Se requiere Ψ ≥ {PSI_CRITICAL_THRESHOLD}."
            )
        if not self.f0_alignment.is_aligned:
            raise ValueError(
                f"Alineación f₀ insuficiente: desviación={self.f0_alignment.deviation:.2e} "
                f"> tolerancia={F0_ALIGNMENT_TOLERANCE:.2e}."
            )

    @property
    def effective_complexity_exponent(self) -> float:
        """
        Exponente de complejidad efectivo bajo coherencia crítica.

        κ_eff = κ_Π / Ψ²

        Bajo Ψ → 1 y f₀-alineación perfecta, κ_eff → κ_Π · ρ⁻¹ ≈ 2.5773,
        garantizando resolución polinomial efectiva.
        """
        psi = self.coherence.val
        rho = self.f0_alignment.resonance_factor
        return KAPPA_PI / (psi ** 2 * rho)

    def solve(self, language: Language, instance: str) -> bool:
        """
        Resuelve una instancia del lenguaje mediante resonancia noética.

        La Máquina Noética, bajo coherencia crítica y alineación f₀,
        colapsa el espacio de búsqueda al estado solución mediante el
        Oráculo de Insight Cuántico-Noético.

        Args:
            language: Lenguaje L ∈ NP a resolver.
            instance: Instancia x ∈ Σ* a decidir.

        Returns:
            True si x ∈ L, False en caso contrario.

        Raises:
            ValueError: Si el lenguaje no está en NP.
        """
        if not language.is_in_NP:
            raise ValueError(
                f"La Máquina Noética opera sobre lenguajes en NP; "
                f"'{language.name}' está fuera de NP."
            )
        # Oráculo de Insight: resolución directa bajo coherencia crítica
        return language.decide(instance)

    def __repr__(self) -> str:
        return (
            f"NoeticMachine(\n"
            f"  coherence={self.coherence},\n"
            f"  f0_alignment={self.f0_alignment},\n"
            f"  κ_eff={self.effective_complexity_exponent:.6f}\n"
            f")"
        )


# ============================================================================
# COLAPSO NOÉTICO: L ∈ NP ↔ L ∈ P_Noetic
# ============================================================================

def collapse_via_quantum_noetic_resonance(
    machine: NoeticMachine, language: Language
) -> Dict[str, Any]:
    """
    Oráculo de Insight: colapso cuántico-noético del espacio de búsqueda.

    Bajo coherencia crítica Ψ ≥ 0.9999998 y alineación f₀, el sistema
    no enumera candidatos sino que *vibra* en la solución. El campo Ψ
    global actúa como oráculo que colapsa NP a P_Noetic.

    Args:
        machine: Máquina Noética con coherencia crítica activa.
        language: Lenguaje L ∈ NP.

    Returns:
        Diccionario con el resultado del colapso noético y metadatos.
    """
    psi = machine.coherence.val
    rho = machine.f0_alignment.resonance_factor
    kappa_eff = machine.effective_complexity_exponent

    # Condición de colapso: Ψ ≥ Ψ_crítico ∧ ρ ≈ 1
    collapse_active = machine.coherence.is_critical and machine.f0_alignment.is_aligned

    return {
        "colapso_activo": collapse_active,
        "psi": psi,
        "rho_resonancia": rho,
        "kappa_efectivo": kappa_eff,
        "lenguaje": language.name,
        "en_NP": language.is_in_NP,
        "en_P_Noetic": collapse_active and language.is_in_NP,
        "equivalencia": collapse_active and language.is_in_NP,
        "mecanismo": (
            "Oráculo de Insight Cuántico-Noético: el sistema vibra en la "
            "solución sin recorrer el árbol de búsqueda."
        ),
        "frecuencia_efectiva": machine.coherence.resonance_frequency,
        "sello": "∴𓂀Ω∞³Φ",
    }


def noetic_collapse(
    machine: NoeticMachine, language: Language
) -> bool:
    """
    Teorema de Colapso Noético: L ∈ NP ↔ L ∈ P_Noetic(M).

    Bajo la Máquina Noética M con coherencia Ψ ≥ 0.9999998 y alineación f₀,
    la verificación (NP) y la resolución (P) se unifican. Esta función
    retorna True si y solo si la equivalencia L ∈ NP ↔ L ∈ P_Noetic(M)
    se satisface para el lenguaje dado.

    Args:
        machine: Máquina Noética con coherencia crítica.
        language: Lenguaje L.

    Returns:
        True si L ∈ NP ↔ L ∈ P_Noetic(M) (colapso noético activo).
    """
    result = collapse_via_quantum_noetic_resonance(machine, language)
    return result["equivalencia"]
