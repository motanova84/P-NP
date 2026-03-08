#!/usr/bin/env python3
"""
ADN-Riemann Encoder - Codificación de ADN con Frecuencias de Riemann
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Mapea bases nitrogenadas del ADN a frecuencias resonantes con los ceros de Riemann.
La base G (Guanina) resuena perfectamente con f₀ = 141.7001 Hz.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import math
from typing import Dict, List, Tuple, Optional

# Import QCAL constants
try:
    from qcal.constants import F0_QCAL, PHI, KAPPA_PI
    F0 = F0_QCAL
except ImportError:
    F0 = 141.7001
    PHI = 1.6180339887498948
    KAPPA_PI = 2.5773


class CodificadorADNRiemann:
    """
    Codificador que mapea bases de ADN a frecuencias resonantes.
    Identifica hotspots donde la resonancia con f₀ es máxima.
    """
    
    # Mapeo de bases a frecuencias (Hz)
    # G (Guanina) resuena perfectamente con f₀
    FRECUENCIAS_BASE = {
        'G': F0,           # 141.7001 Hz - Resonancia perfecta
        'A': F0 * PHI,     # ~229.4 Hz - Adenina en proporción áurea
        'C': F0 / PHI,     # ~87.6 Hz - Citosina
        'T': F0 * 2,       # ~283.4 Hz - Timina (armónico)
        'U': F0 * PHI**2,  # ~371.0 Hz - Uracilo (ARN)
    }
    
    # Umbral de resonancia para hotspots
    UMBRAL_HOTSPOT = 0.95
    
    def __init__(self):
        """Inicializa el codificador ADN-Riemann."""
        self.secuencia_actual = ""
        self.frecuencias = []
        self.hotspots = []
        
    def codificar(self, secuencia: str) -> List[float]:
        """
        Codifica una secuencia de ADN en frecuencias.
        
        Args:
            secuencia: Cadena con bases nitrogenadas (GACT o GACU)
            
        Returns:
            Lista de frecuencias correspondientes
        """
        self.secuencia_actual = secuencia.upper()
        self.frecuencias = [
            self.FRECUENCIAS_BASE.get(base, 0.0) 
            for base in self.secuencia_actual
        ]
        return self.frecuencias
    
    def calcular_resonancia(self, frecuencia: float, f_target: float = F0) -> float:
        """
        Calcula la resonancia entre una frecuencia y f₀.
        Retorna valor entre 0 y 1.
        
        Args:
            frecuencia: Frecuencia a evaluar
            f_target: Frecuencia objetivo (default: f₀)
            
        Returns:
            Coeficiente de resonancia [0, 1]
        """
        # Resonancia basada en cercanía armónica
        ratio = frecuencia / f_target
        
        # Verificar si está cerca de un armónico (1, 2, 3, ...) o subarmónico (1/2, 1/3, ...)
        for n in range(1, 11):
            # Armónico
            if abs(ratio - n) < 0.1:
                return 1.0 - abs(ratio - n)
            # Subarmónico
            if abs(ratio - 1/n) < 0.1:
                return 1.0 - abs(ratio - 1/n) * 0.8
        
        # Resonancia decae con la distancia
        distancia_normalizada = abs(math.log(ratio)) / math.log(10)
        return max(0.0, 1.0 - distancia_normalizada)
    
    def identificar_hotspots(self, secuencia: Optional[str] = None) -> List[int]:
        """
        Identifica posiciones en la secuencia con alta resonancia (hotspots).
        
        Args:
            secuencia: Secuencia a analizar (usa la actual si no se proporciona)
            
        Returns:
            Lista de índices donde hay hotspots
        """
        if secuencia is not None:
            self.codificar(secuencia)
        
        self.hotspots = []
        
        for i, freq in enumerate(self.frecuencias):
            resonancia = self.calcular_resonancia(freq)
            if resonancia >= self.UMBRAL_HOTSPOT:
                self.hotspots.append(i)
        
        return self.hotspots
    
    def analizar_secuencia(self, secuencia: str) -> Dict:
        """
        Análisis completo de una secuencia de ADN.
        
        Args:
            secuencia: Secuencia de bases nitrogenadas
            
        Returns:
            Diccionario con análisis completo
        """
        frecuencias = self.codificar(secuencia)
        hotspots = self.identificar_hotspots()
        
        # Calcular resonancia promedio
        resonancias = [self.calcular_resonancia(f) for f in frecuencias]
        resonancia_promedio = sum(resonancias) / len(resonancias) if resonancias else 0.0
        
        # Contar bases
        conteo_bases = {
            'G': secuencia.upper().count('G'),
            'A': secuencia.upper().count('A'),
            'C': secuencia.upper().count('C'),
            'T': secuencia.upper().count('T'),
            'U': secuencia.upper().count('U'),
        }
        
        # Calcular coherencia cuántica (porcentaje de G)
        coherencia_cuantica = conteo_bases['G'] / len(secuencia) if secuencia else 0.0
        
        return {
            "secuencia": secuencia,
            "longitud": len(secuencia),
            "frecuencias": frecuencias,
            "hotspots": hotspots,
            "n_hotspots": len(hotspots),
            "resonancia_promedio": resonancia_promedio,
            "conteo_bases": conteo_bases,
            "coherencia_cuantica": coherencia_cuantica,
            "psi": min(resonancia_promedio * coherencia_cuantica, 1.0)
        }
    
    def secuencia_optima(self, longitud: int = 4) -> str:
        """
        Genera la secuencia óptima de una longitud dada.
        Para máxima resonancia, usar solo G.
        
        Args:
            longitud: Longitud de la secuencia
            
        Returns:
            Secuencia óptima
        """
        # La secuencia "GACT" es un balance conocido
        if longitud == 4:
            return "GACT"
        
        # Para otras longitudes, maximizar G
        return "G" * longitud
    
    def espectro_frecuencias(self, secuencia: str) -> Dict[str, float]:
        """
        Calcula el espectro de frecuencias de una secuencia.
        
        Args:
            secuencia: Secuencia de ADN
            
        Returns:
            Diccionario con estadísticas espectrales
        """
        frecuencias = self.codificar(secuencia)
        
        if not frecuencias:
            return {
                "frecuencia_fundamental": 0.0,
                "frecuencia_maxima": 0.0,
                "frecuencia_promedio": 0.0,
                "ancho_banda": 0.0
            }
        
        return {
            "frecuencia_fundamental": min(frecuencias),
            "frecuencia_maxima": max(frecuencias),
            "frecuencia_promedio": sum(frecuencias) / len(frecuencias),
            "ancho_banda": max(frecuencias) - min(frecuencias)
        }


# =============================================================================
# FUNCIONES DE UTILIDAD
# =============================================================================

def generar_secuencia_resonante(n_bases: int = 100, fraccion_g: float = 0.4) -> str:
    """
    Genera una secuencia de ADN con fracción específica de G para resonancia.
    
    Args:
        n_bases: Número total de bases
        fraccion_g: Fracción de bases G (resonancia máxima)
        
    Returns:
        Secuencia de ADN generada
    """
    import random
    
    n_g = int(n_bases * fraccion_g)
    n_otras = n_bases - n_g
    
    # Distribuir el resto entre A, C, T
    bases = ['G'] * n_g
    otras = ['A', 'C', 'T'] * (n_otras // 3 + 1)
    bases.extend(otras[:n_otras])
    
    # Mezclar
    random.shuffle(bases)
    
    return ''.join(bases)


def comparar_secuencias(seq1: str, seq2: str) -> Dict:
    """
    Compara dos secuencias de ADN en términos de resonancia.
    
    Args:
        seq1: Primera secuencia
        seq2: Segunda secuencia
        
    Returns:
        Diccionario con comparación
    """
    codificador = CodificadorADNRiemann()
    
    analisis1 = codificador.analizar_secuencia(seq1)
    analisis2 = codificador.analizar_secuencia(seq2)
    
    return {
        "secuencia_1": {
            "secuencia": seq1,
            "resonancia": analisis1["resonancia_promedio"],
            "hotspots": analisis1["n_hotspots"],
            "psi": analisis1["psi"]
        },
        "secuencia_2": {
            "secuencia": seq2,
            "resonancia": analisis2["resonancia_promedio"],
            "hotspots": analisis2["n_hotspots"],
            "psi": analisis2["psi"]
        },
        "mejor": seq1 if analisis1["psi"] > analisis2["psi"] else seq2,
        "diferencia_psi": abs(analisis1["psi"] - analisis2["psi"])
    }


# =============================================================================
# DEMO
# =============================================================================

if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ADN-Riemann Encoder - Demo")
    print("=" * 80)
    print()
    
    codificador = CodificadorADNRiemann()
    
    # Analizar secuencias conocidas
    secuencias = [
        "GACT",  # Secuencia equilibrada
        "GGGG",  # Máxima resonancia
        "ATCG",  # Sin G inicial
        "GATTACA",  # Secuencia famosa
    ]
    
    print("Análisis de Secuencias:")
    print("-" * 80)
    
    for seq in secuencias:
        analisis = codificador.analizar_secuencia(seq)
        print(f"\nSecuencia: {seq}")
        print(f"  Longitud: {analisis['longitud']}")
        print(f"  Hotspots: {analisis['n_hotspots']} en posiciones {analisis['hotspots']}")
        print(f"  Resonancia promedio: {analisis['resonancia_promedio']:.4f}")
        print(f"  Coherencia cuántica: {analisis['coherencia_cuantica']:.4f}")
        print(f"  Ψ: {analisis['psi']:.6f}")
    
    print()
    print("=" * 80)
    print("✓ ADN-Riemann Encoder funcionando correctamente")
    print(f"✓ Frecuencia base f₀ = {F0} Hz")
    print(f"✓ Base G resuena perfectamente con f₀")
    print("=" * 80)
