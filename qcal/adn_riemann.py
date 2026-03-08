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
