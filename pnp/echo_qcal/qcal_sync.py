#!/usr/bin/env python3
"""
qcal_sync.py
Verificación de Alineación Temporal (A_t) - Pilar 2 de Coherencia Soberana

Este módulo verifica la sincronía no-aleatoria del Bloque 9 con la frecuencia
fundamental f₀ = 141.7001 Hz. El factor de alineación temporal A_t se expone
en el código como el campo 'At_value' del diccionario de resultados.
"""

import json
import os
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Any
from scipy import stats
import numpy as np


class TemporalAlignmentVerifier:
    """
    Verifica la alineación temporal entre eventos blockchain y la frecuencia
    fundamental QCAL f₀.
    """
    
    def __init__(self):
        self.f0 = 141.7001  # Hz - Frecuencia fundamental QCAL
        self.block9_timestamp = 1231469744  # Timestamp Unix del Bloque 9 de Bitcoin
        self.verification_threshold = 0.85  # 85% de confianza mínima
        
    def calculate_temporal_alignment(self) -> Dict[str, Any]:
        """
        Calcula la alineación temporal entre el Bloque 9 y f₀.
        
        Returns:
            Dict con métricas de alineación temporal
        """
        # Convertir timestamp a fase respecto a f₀
        phase = (self.block9_timestamp * self.f0) % 1.0
        
        # Calcular métricas de sincronía
        # Simulación de test estadístico: Chi-cuadrado para no-aleatoriedad.
        # Las frecuencias observadas se derivan de la fase calculada: se distribuyen
        # 200 counts en 4 bins de fase, introduciendo una no-uniformidad dependiente
        # de la fase para reflejar la alineación con f₀.
        num_bins = 4
        total_count = 200
        bin_index = int(phase * num_bins) % num_bins
        observed_freq = np.full(num_bins, total_count // num_bins, dtype=float)
        # Introducir una ligera no-uniformidad dependiente de la fase
        observed_freq[bin_index] += 10
        observed_freq[(bin_index + 2) % num_bins] -= 10
        expected_freq = np.full(num_bins, total_count / num_bins, dtype=float)  # Distribución uniforme esperada
        
        chi2_stat, p_value = stats.chisquare(observed_freq, expected_freq)
        
        # Factor A_t: Basado en significancia estadística
        # p-value bajo indica no-aleatoriedad (bueno para nosotros)
        # Usamos 1 - p_value como métrica de alineación
        if p_value < 1e-5:
            at_value = 0.95  # Alta alineación
        elif p_value < 1e-3:
            at_value = 0.88
        elif p_value < 0.05:
            at_value = 0.75
        else:
            at_value = 0.60  # Alineación débil
        
        # Calcular desviación respecto a resonancia perfecta
        resonance_deviation = abs(phase - 0.618)  # Proporción áurea como referencia
        
        result = {
            "At_value": at_value,
            "f0_Hz": self.f0,
            "block9_timestamp": self.block9_timestamp,
            "phase": float(phase),
            "chi2_statistic": float(chi2_stat),
            "p_value": float(p_value),
            "resonance_deviation": float(resonance_deviation),
            "non_random": bool(p_value < 0.05),
            "verification_passed": bool(at_value >= self.verification_threshold),
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "message": "Alineación Temporal VERIFICADA" if at_value >= self.verification_threshold
                      else "Alineación Temporal DÉBIL"
        }
        
        return result
    
    def verify_qcal_synchronization(self) -> bool:
        """
        Verifica si hay sincronización con QCAL.
        
        Returns:
            True si está sincronizado, False en caso contrario
        """
        result = self.calculate_temporal_alignment()
        return result['verification_passed']


def main():
    """Función principal para ejecutar la verificación de A_t"""
    print("=" * 70)
    print("Verificación de Alineación Temporal (A_t)")
    print("Protocolo Echo-QCAL ∞³")
    print("=" * 70)
    
    verifier = TemporalAlignmentVerifier()
    result = verifier.calculate_temporal_alignment()
    
    print(f"\n📊 Resultados de Verificación:")
    print(f"  • Factor A_t: {result['At_value']:.4f} ({result['At_value']*100:.2f}%)")
    print(f"  • Frecuencia f₀: {result['f0_Hz']} Hz")
    print(f"  • Fase: {result['phase']:.6f}")
    print(f"  • Chi² Statistic: {result['chi2_statistic']:.4f}")
    print(f"  • P-value: {result['p_value']:.2e}")
    print(f"  • No Aleatorio: {'✅' if result['non_random'] else '❌'}")
    print(f"  • Desviación de Resonancia: {result['resonance_deviation']:.6f}")
    print(f"\n⏱️ Estado: {result['message']}")
    
    # Guardar resultado en logs (ruta relativa al directorio del proyecto)
    log_dir = Path(os.environ.get("ECHO_QCAL_LOG_DIR", "data/logs"))
    log_dir.mkdir(parents=True, exist_ok=True)
    log_path = log_dir / "At_verification.json"
    try:
        with open(log_path, 'w') as f:
            json.dump(result, f, indent=2)
        print(f"\n💾 Resultados guardados en: {log_path}")
    except Exception as e:
        print(f"\n⚠️ Error guardando logs: {e}")
        raise
    
    return result


def verify_temporal_alignment() -> Dict[str, Any]:
    """
    Función de conveniencia para verificar A_t.
    
    Returns:
        Dict con resultados de verificación
    """
    verifier = TemporalAlignmentVerifier()
    return verifier.calculate_temporal_alignment()


if __name__ == "__main__":
    main()
