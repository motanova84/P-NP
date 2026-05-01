#!/usr/bin/env python3
"""
resonant_nexus_engine.py
Arquitectura Unitaria (A_u) - Pilar 3 de Coherencia Soberana

Este módulo simula la composición armónica y la volatilidad coherente
del sistema QCAL ∞³. El factor de arquitectura unitaria A_u se expone
como el campo 'Au_value' en los diccionarios de resultados.
"""

import json
import os
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Any
import numpy as np


# Constantes QCAL
F0_HZ = 141.7001        # Frecuencia fundamental
KAPPA_PI = 2.5773       # Constante universal de Calabi-Yau
SIGMA_COHERENT = 0.04   # Volatilidad coherente


class ResonantNexusEngine:
    """
    Simula la arquitectura unitaria del sistema QCAL.
    Verifica la composición armónica y la volatilidad coherente del nexo resonante.
    """

    def __init__(self, f0: float = F0_HZ, kappa: float = KAPPA_PI,
                 sigma: float = SIGMA_COHERENT):
        self.f0 = f0
        self.kappa = kappa
        self.sigma = sigma
        self.verification_threshold = 0.85  # 85% de confianza mínima

    def compute_harmonic_composition(self, n_harmonics: int = 7) -> Dict[str, Any]:
        """
        Calcula la composición armónica del nexo resonante.

        Args:
            n_harmonics: Número de armónicos a calcular

        Returns:
            Dict con amplitudes y coherencia armónica
        """
        harmonics = []
        total_power = 0.0
        coherent_power = 0.0

        for k in range(1, n_harmonics + 1):
            freq = self.f0 * k
            # Amplitud: decae según κ_π para armónicos superiores
            amplitude = 1.0 / (self.kappa ** (k - 1))
            # Fase coherente: múltiplo de 2π normalizado
            phase = (2 * np.pi * k / self.kappa) % (2 * np.pi)
            power = amplitude ** 2
            total_power += power
            # Consideramos coherente si la amplitud supera un umbral mínimo
            if amplitude >= 0.1:
                coherent_power += power
            harmonics.append({
                "k": k,
                "frequency_Hz": freq,
                "amplitude": amplitude,
                "phase_rad": phase,
                "power": power,
            })

        coherence_ratio = coherent_power / total_power if total_power > 0 else 0.0
        return {"harmonics": harmonics, "coherence_ratio": coherence_ratio,
                "total_power": total_power}

    def compute_coherent_volatility(self, n_samples: int = 1000) -> Dict[str, Any]:
        """
        Simula la volatilidad coherente del sistema.

        Args:
            n_samples: Número de muestras de simulación

        Returns:
            Dict con estadísticas de volatilidad
        """
        rng = np.random.default_rng(seed=42)
        # Precio simulado con volatilidad coherente
        returns = rng.normal(0, self.sigma, n_samples)
        # Verificar que la volatilidad está dentro del rango coherente
        observed_sigma = float(np.std(returns))
        sigma_deviation = abs(observed_sigma - self.sigma) / self.sigma
        # Coherente si la desviación es menor al 10%
        volatility_coherent = sigma_deviation < 0.10
        return {
            "target_sigma": self.sigma,
            "observed_sigma": float(observed_sigma),
            "sigma_deviation_pct": float(sigma_deviation * 100),
            "volatility_coherent": bool(volatility_coherent),
        }

    def calculate_unitary_architecture(self) -> Dict[str, Any]:
        """
        Calcula el factor de Arquitectura Unitaria A_u.

        Returns:
            Dict con métricas de arquitectura unitaria
        """
        harmonic_data = self.compute_harmonic_composition()
        volatility_data = self.compute_coherent_volatility()

        coherence_ratio = harmonic_data["coherence_ratio"]
        volatility_coherent = volatility_data["volatility_coherent"]

        # Factor A_u: combinación de coherencia armónica y volatilidad
        au_value = coherence_ratio * (1.0 if volatility_coherent else 0.8)
        # Clamp a [0, 1]
        au_value = min(max(au_value, 0.0), 1.0)

        result = {
            "Au_value": float(au_value),
            "f0_Hz": self.f0,
            "kappa_pi": self.kappa,
            "coherence_ratio": float(coherence_ratio),
            "volatility_coherent": volatility_coherent,
            "observed_sigma": float(volatility_data["observed_sigma"]),
            "verification_passed": au_value >= self.verification_threshold,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "message": (
                "Arquitectura Unitaria VERIFICADA"
                if au_value >= self.verification_threshold
                else "Arquitectura Unitaria DÉBIL"
            ),
        }
        return result


def main():
    """Función principal para ejecutar la verificación de A_u"""
    print("=" * 70)
    print("Verificación de Arquitectura Unitaria (A_u)")
    print("Protocolo Echo-QCAL ∞³")
    print("=" * 70)

    engine = ResonantNexusEngine()
    result = engine.calculate_unitary_architecture()

    print(f"\n📊 Resultados de Verificación:")
    print(f"  • Factor A_u: {result['Au_value']:.4f} ({result['Au_value']*100:.2f}%)")
    print(f"  • Frecuencia f₀: {result['f0_Hz']} Hz")
    print(f"  • κ_π: {result['kappa_pi']}")
    print(f"  • Coherencia Armónica: {result['coherence_ratio']:.4f}")
    print(f"  • Volatilidad Coherente: {'✅' if result['volatility_coherent'] else '❌'}")
    print(f"  • σ Observado: {result['observed_sigma']:.4f}")
    print(f"\n⚛️ Estado: {result['message']}")

    # Guardar resultado en logs (ruta configurable vía variable de entorno)
    log_dir = Path(os.environ.get("ECHO_QCAL_LOG_DIR", "data/logs"))
    log_dir.mkdir(parents=True, exist_ok=True)
    log_path = log_dir / "Au_verification.json"
    try:
        with open(log_path, 'w') as f:
            json.dump(result, f, indent=2)
        print(f"\n💾 Resultados guardados en: {log_path}")
    except Exception as e:
        print(f"\n⚠️ Error guardando logs: {e}")
        raise

    return result


def verify_unitary_architecture() -> Dict[str, Any]:
    """
    Función de conveniencia para verificar A_u.

    Returns:
        Dict con resultados de verificación
    """
    engine = ResonantNexusEngine()
    return engine.calculate_unitary_architecture()


if __name__ == "__main__":
    main()
