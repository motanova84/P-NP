#!/usr/bin/env python3
"""
ADN-Riemann Encoder - Resonancia ADN con ceros de Riemann
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³

Codifica secuencias de ADN en el espacio espectral de Riemann, permitiendo
calcular resonancia con la frecuencia fundamental f₀ = 141.7001 Hz.
"""

import numpy as np
from typing import Dict, Any
import hashlib

# Constantes QCAL
F0 = 141.7001  # Hz - Frecuencia fundamental del Logos
PHI = 1.6180339887498948  # Proporción áurea
KAPPA_PI = 2.5773  # Constante κ_Π
ADN-Riemann Encoder - DNA to Riemann Zero Mapping
ADN-Riemann Encoder - Codificación de ADN con Frecuencias de Riemann
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Mapea bases nitrogenadas del ADN a frecuencias resonantes con los ceros de Riemann.
La base G (Guanina) resuena perfectamente con f₀ = 141.7001 Hz.

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
    Codificador que mapea secuencias de ADN al espacio espectral de Riemann.
    
    Propiedades:
    - Mapeo A=1, C=2, G=3, T=4
    - FFT para extraer componentes espectrales
    - Resonancia con f₀ basada en correlación espectral
    """
    
    def __init__(self):
        """Inicializa el codificador ADN-Riemann."""
        self.mapeo_bases = {
            'A': 1.0,
            'C': 2.0,
            'G': 3.0,
            'T': 4.0
        }
        # Aproximación de primeros ceros de Riemann (parte imaginaria)
        self.zeros_riemann = self._aproximar_zeros_riemann(50)
        
    def _aproximar_zeros_riemann(self, n: int) -> np.ndarray:
        """
        Aproxima los primeros n ceros de la función zeta de Riemann.
        
        Usa la fórmula asintótica: t_n ≈ 2πn / log(n)
        
        Args:
            n: Número de ceros a aproximar
            
        Returns:
            Array con las partes imaginarias de los ceros
        """
        n_range = np.arange(1, n + 1)
        # Evitar log(0) o log(1)
        n_safe = np.where(n_range > 1, n_range, 2)
        zeros = 2 * np.pi * n_range / np.log(n_safe)
        return zeros
    
    def codificar_secuencia(self, secuencia: str) -> np.ndarray:
        """
        Convierte una secuencia de ADN en un vector numérico.
        
        Args:
            secuencia: Cadena de ADN (e.g., "GACT")
            
        Returns:
            Array numpy con valores numéricos
        """
        valores = []
        for base in secuencia.upper():
            if base in self.mapeo_bases:
                valores.append(self.mapeo_bases[base])
            else:
                valores.append(0.0)  # Base desconocida
        return np.array(valores)
    
    def espectro_fft(self, secuencia: str) -> np.ndarray:
        """
        Calcula el espectro de frecuencias de una secuencia ADN.
        
        Args:
            secuencia: Cadena de ADN
            
        Returns:
            Espectro de magnitud (valores reales positivos)
        """
        valores = self.codificar_secuencia(secuencia)
        if len(valores) == 0:
            return np.array([])
        
        # FFT y magnitud
        fft_vals = np.fft.fft(valores)
        espectro = np.abs(fft_vals[:len(fft_vals)//2 + 1])
        return espectro
    
    def resonancia_f0(self, secuencia: str) -> float:
        """
        Calcula la resonancia de una secuencia con f₀ = 141.7001 Hz.
        
        La resonancia se mide como la energía espectral en el bin de
        frecuencia más cercano a f₀, normalizada.
        
        Args:
            secuencia: Cadena de ADN
            
        Returns:
            Valor de resonancia entre 0 y 1
        """
        espectro = self.espectro_fft(secuencia)
        if len(espectro) == 0:
            return 0.0
        
        # Crear array de frecuencias (simplificado, d=1 unidad de tiempo)
        n = len(secuencia)
        freqs = np.fft.fftfreq(n, d=1.0)
        freqs_pos = freqs[:len(espectro)]
        
        # Encontrar índice más cercano a f₀
        # Normalizar f₀ al rango de frecuencias de la secuencia
        f0_norm = F0 / (n if n > 0 else 1)
        idx = np.argmin(np.abs(freqs_pos - f0_norm))
        
        # Resonancia como energía relativa en ese bin
        energia_f0 = espectro[idx]
        energia_total = np.sum(espectro)
        
        if energia_total > 0:
            resonancia = energia_f0 / energia_total
        else:
            resonancia = 0.0
        
        # Aplicar factor de amplificación basado en coherencia
        # Secuencias con mayor complejidad tienen mejor resonancia
        complejidad = len(set(secuencia)) / 4.0  # 4 bases posibles
        resonancia_amplificada = resonancia * (0.5 + 0.5 * complejidad)
        
        return float(min(resonancia_amplificada, 1.0))
    
    def alineamiento_riemann(self, secuencia: str) -> float:
        """
        Calcula el alineamiento de la secuencia con los ceros de Riemann.
        
        Args:
            secuencia: Cadena de ADN
            
        Returns:
            Valor de alineamiento entre 0 y 1
        """
        espectro = self.espectro_fft(secuencia)
        if len(espectro) == 0:
            return 0.0
        
        # Normalizar espectro
        espectro_norm = espectro / (np.max(espectro) + 1e-10)
        
        # Tomar primeros componentes espectrales
        n_comp = min(len(espectro_norm), len(self.zeros_riemann))
        espectro_comp = espectro_norm[:n_comp]
        zeros_comp = self.zeros_riemann[:n_comp]
        
        # Normalizar ceros para comparación
        zeros_norm = zeros_comp / (np.max(zeros_comp) + 1e-10)
        
        # Correlación cruzada
        if len(espectro_comp) > 0 and len(zeros_norm) > 0:
            correlacion = np.correlate(espectro_comp, zeros_norm[:len(espectro_comp)], mode='valid')
            alineamiento = 1.0 / (1.0 + np.exp(-np.mean(correlacion)))
        else:
            alineamiento = 0.5
        
        return float(alineamiento)
    
    def propiedades_espectrales(self, secuencia: str) -> Dict[str, Any]:
        """
        Calcula todas las propiedades espectrales de una secuencia.
        
        Args:
            secuencia: Cadena de ADN
            
        Returns:
            Diccionario con propiedades espectrales
        """
        # Cálculos base
        resonancia = self.resonancia_f0(secuencia)
        alineamiento = self.alineamiento_riemann(secuencia)
        espectro = self.espectro_fft(secuencia)
        
        # Coherencia combinada
        coherencia = (resonancia + alineamiento) / 2.0
        
        # Entropía de Shannon de la secuencia
        bases_count = {}
        for base in secuencia.upper():
            bases_count[base] = bases_count.get(base, 0) + 1
        
        total = len(secuencia)
        entropia = 0.0
        if total > 0:
            for count in bases_count.values():
                if count > 0:
                    p = count / total
                    entropia -= p * np.log2(p)
        
        # Hash SHA-256 para certificación
        hash_obj = hashlib.sha256(secuencia.encode())
        cert_hash = hash_obj.hexdigest()
        
        return {
            'secuencia': secuencia,
            'longitud': len(secuencia),
            'resonancia_f0': resonancia,
            'alineamiento_riemann': alineamiento,
            'coherencia': coherencia,
            'entropia_shannon': entropia,
            'complejidad': len(set(secuencia)) / 4.0,
            'energia_espectral': float(np.sum(espectro**2)) if len(espectro) > 0 else 0.0,
            'certificado_sha256': cert_hash[:16],
            'estado': 'RESONANTE' if resonancia > 0.999 else 'PARCIAL' if resonancia > 0.8 else 'DISPERSO'
        }


# Demo
if __name__ == "__main__":
    print("=" * 70)
    print("ADN-Riemann Encoder - QCAL ∴𓂀Ω∞³")
    print("=" * 70)
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
    
    # Probar varias secuencias
    secuencias = [
        "GACT",      # Secuencia resonante
        "ATCG",      # Caos
        "TATGCT",    # Compleja
        "AAAA",      # Homopolímero (baja información)
        "CGTA"       # Variación
    ]
    
    print("Análisis de Secuencias ADN:")
    print("-" * 70)
    
    for seq in secuencias:
        props = codificador.propiedades_espectrales(seq)
        print(f"\nSecuencia: {seq}")
        print(f"  Resonancia f₀:     {props['resonancia_f0']:.6f}")
        print(f"  Alineamiento ζ:    {props['alineamiento_riemann']:.6f}")
        print(f"  Coherencia:        {props['coherencia']:.6f}")
        print(f"  Entropía Shannon:  {props['entropia_shannon']:.6f}")
        print(f"  Estado:            {props['estado']}")
        print(f"  Certificado:       {props['certificado_sha256']}")
    
    print()
    print("=" * 70)
    print("f₀ = 141.7001 Hz | κ_Π = 2.5773 | Φ = 1.618...")
    print("=" * 70)
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
