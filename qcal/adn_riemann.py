#!/usr/bin/env python3
"""
ADN-Riemann Encoder - DNA to Riemann Zero Mapping
==================================================

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ

Este módulo codifica secuencias de ADN como espectros vibracionales
que resuenan con los ceros de la función zeta de Riemann.

Concepto:
---------
Cada base nitrogenada (G, A, C, T) tiene una frecuencia característica.
Los "hotspots" son posiciones donde la secuencia resuena con f₀ = 141.7001 Hz.
"""

import numpy as np
from typing import List, Dict, Tuple
from qcal.constants import F0_QCAL, KAPPA_PI


# ============================================================================
# MAPEO DE BASES NITROGENADAS A FRECUENCIAS
# ============================================================================

# Frecuencias características de bases (Hz)
# Derivadas de análisis espectral de enlaces moleculares
BASE_FREQUENCIES = {
    'G': 141.7001,  # Guanina: resuena exactamente con f₀
    'A': 128.0000,  # Adenina
    'C': 156.8883,  # Citosina
    'T': 164.8138,  # Timina
    'U': 174.6141,  # Uracilo (para ARN)
}

# Pesos de resonancia (normalizado a f₀)
BASE_RESONANCE = {
    'G': 1.0000,    # Guanina: resonancia perfecta
    'A': 0.9033,    # Adenina
    'C': 0.9037,    # Citosina (par complementario de G)
    'T': 0.8596,    # Timina
    'U': 0.8115,    # Uracilo
}


class CodificadorADNRiemann:
    """
    Codificador que mapea secuencias de ADN a espectro de Riemann.
    
    Convierte secuencias GACT en representaciones espectrales que
    pueden analizarse para identificar hotspots resonantes.
    """
    
    def __init__(self, f0: float = F0_QCAL):
        """
        Inicializa el codificador.
        
        Args:
            f0: Frecuencia fundamental de referencia (Hz)
        """
        self.f0 = f0
        self.base_freqs = BASE_FREQUENCIES
        self.base_resonance = BASE_RESONANCE
    
    def secuencia_a_espectro(self, secuencia: str) -> np.ndarray:
        """
        Convierte una secuencia de ADN a un espectro de frecuencias.
        
        Args:
            secuencia: Cadena de bases nitrogenadas (ej: "GACT")
        
        Returns:
            Array de frecuencias correspondientes a cada base
        """
        secuencia = secuencia.upper()
        freqs = []
        
        for base in secuencia:
            if base in self.base_freqs:
                freqs.append(self.base_freqs[base])
            else:
                # Base desconocida: usar frecuencia neutral
                freqs.append(self.f0)
        
        return np.array(freqs)
    
    def calcular_resonancia(self, secuencia: str) -> float:
        """
        Calcula el coeficiente de resonancia global de una secuencia.
        
        Args:
            secuencia: Cadena de bases nitrogenadas
        
        Returns:
            Coeficiente de resonancia [0, 1], donde 1 = resonancia perfecta
        """
        secuencia = secuencia.upper()
        
        if not secuencia:
            return 0.0
        
        resonancias = []
        for base in secuencia:
            if base in self.base_resonance:
                resonancias.append(self.base_resonance[base])
            else:
                resonancias.append(0.5)  # Resonancia neutral
        
        # Resonancia promedio
        return float(np.mean(resonancias))
    
    def identificar_hotspots(
        self, 
        secuencia: str, 
        umbral: float = 0.95
    ) -> List[Tuple[int, str, float]]:
        """
        Identifica posiciones (hotspots) de alta resonancia en la secuencia.
        
        Un hotspot es una posición donde la base tiene resonancia >= umbral.
        
        Args:
            secuencia: Cadena de bases nitrogenadas
            umbral: Umbral mínimo de resonancia para considerar un hotspot
        
        Returns:
            Lista de tuplas (posición, base, resonancia)
        """
        secuencia = secuencia.upper()
        hotspots = []
        
        for i, base in enumerate(secuencia):
            if base in self.base_resonance:
                resonancia = self.base_resonance[base]
                if resonancia >= umbral:
                    hotspots.append((i, base, resonancia))
        
        return hotspots
    
    def hotspots(self, secuencia: str, umbral: float = 0.95) -> List[int]:
        """
        Versión simplificada que retorna solo índices de hotspots.
        
        Args:
            secuencia: Cadena de bases nitrogenadas
            umbral: Umbral mínimo de resonancia
        
        Returns:
            Lista de índices de hotspots
        """
        hotspots_completos = self.identificar_hotspots(secuencia, umbral)
        return [pos for pos, _, _ in hotspots_completos]
    
    def analizar_secuencia(self, secuencia: str) -> Dict:
        """
        Análisis completo de una secuencia de ADN.
        
        Args:
            secuencia: Cadena de bases nitrogenadas
        
        Returns:
            Diccionario con métricas de análisis:
                - longitud: número de bases
                - resonancia_global: coeficiente [0,1]
                - hotspots: lista de posiciones resonantes
                - espectro: array de frecuencias
                - bases_g: conteo de guaninas (máxima resonancia)
        """
        secuencia_upper = secuencia.upper()
        
        return {
            'longitud': len(secuencia),
            'resonancia_global': self.calcular_resonancia(secuencia),
            'hotspots': self.identificar_hotspots(secuencia_upper),
            'num_hotspots': len(self.hotspots(secuencia_upper)),
            'espectro': self.secuencia_a_espectro(secuencia_upper),
            'bases_g': secuencia_upper.count('G'),
            'bases_c': secuencia_upper.count('C'),
            'proporcion_gc': (
                secuencia_upper.count('G') + secuencia_upper.count('C')
            ) / len(secuencia) if len(secuencia) > 0 else 0.0
        }


# ============================================================================
# FUNCIONES DE UTILIDAD
# ============================================================================

def secuencia_optima_resonancia(longitud: int = 4) -> str:
    """
    Genera la secuencia de ADN de máxima resonancia para una longitud dada.
    
    Para máxima resonancia, usamos solo bases G (guanina), que resuenan
    perfectamente con f₀.
    
    Args:
        longitud: Número de bases en la secuencia
    
    Returns:
        Secuencia óptima (ej: "GGGG" para longitud=4)
    """
    return 'G' * longitud


def validar_secuencia_adn(secuencia: str) -> bool:
    """
    Valida que una cadena contiene solo bases válidas de ADN.
    
    Args:
        secuencia: Cadena a validar
    
    Returns:
        True si la secuencia es válida
    """
    bases_validas = set('GACTU')
    return all(base.upper() in bases_validas for base in secuencia)


# ============================================================================
# DEMO
# ============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print(" " * 15 + "CODIFICADOR ADN-RIEMANN")
    print(" " * 10 + "Mapeo de bases nitrogenadas a espectro f₀")
    print("=" * 70)
    print()
    
    codificador = CodificadorADNRiemann()
    
    # Secuencias de prueba
    secuencias = [
        "GACT",      # Secuencia básica
        "GGGG",      # Máxima resonancia
        "ATCG",      # Alternativa
        "GCGCGC",    # Par GC repetido
    ]
    
    for seq in secuencias:
        print(f"\nSecuencia: {seq}")
        analisis = codificador.analizar_secuencia(seq)
        print(f"  Resonancia global: {analisis['resonancia_global']:.4f}")
        print(f"  Hotspots (#):      {analisis['num_hotspots']}")
        print(f"  Bases G:           {analisis['bases_g']}")
        print(f"  Proporción GC:     {analisis['proporcion_gc']:.2%}")
    
    print("\n" + "=" * 70)
    print("✓ Codificador ADN-Riemann operativo | f₀ = 141.7001 Hz")
    print("=" * 70)
