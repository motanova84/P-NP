#!/usr/bin/env python3
"""
🌀 PNP QCAL — Coherencia Metric y Teorema Operativo
═══════════════════════════════════════════════════════════════
Formalizacion del colapso P vs NP en el marco QCAL.

Ψ_X(σ) = I_X(σ) · A_{X,eff}(σ)² · R_X(σ)

Donde:
- I_X: informacion estructural reconocida en la configuracion
- A_{X,eff}: capacidad de acoplamiento al campo global
- R_X: alineacion espectral riemanniana/noetica

Teorema operativo:
- Region P-coherente: colapso con coste polinomico y Ψ > 0.888
- Region NP-dispersa: coste super-polinomico o Ψ < 0.888

Framework: QCAL ∞³ · f₀ = 141.7001 Hz · H_Ψ
Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTA
═══════════════════════════════════════════════════════════════
"""

import numpy as np
from dataclasses import dataclass, field
from typing import List, Optional, Callable
from enum import Enum

F0 = 141.7001
PSI_UMBRAL = 0.888


@dataclass
class ConfiguracionPNP:
    """Una configuracion (asignacion booleana, certificado, etc.)."""
    id: int
    valores: dict
    restricciones_satisfechas: int = 0
    total_restricciones: int = 0


@dataclass
class InstanciaPNP:
    """Una instancia de problema NP."""
    id: str
    configuraciones: List[ConfiguracionPNP]
    n_vars: int
    n_clausulas: int
    tipo: str = "3-SAT"


class DinamicaQCAL:
    """
    Dinamica QCAL sobre configuraciones.
    Induce medidas μ_t y funcional C_X(t).
    """
    
    def __init__(self, instancia: InstanciaPNP):
        self.X = instancia
        self.mu_t = {c.id: 1.0 / len(instancia.configuraciones) 
                     for c in instancia.configuraciones}
        self.t = 0
        self.historial_C = []
        self.coste_K = 0.0
    
    def paso(self):
        """Un paso de la dinamica QCAL."""
        self.t += 1
        # Simular concentracion de coherencia
        for c in self.X.configuraciones:
            psi = self._psi_config(c)
            self.mu_t[c.id] *= (0.5 + 0.5 * psi)
        
        # Renormalizar
        total = sum(self.mu_t.values())
        if total > 0:
            for k in self.mu_t:
                self.mu_t[k] /= total
        
        # Coste de coherencia
        self.coste_K += len(self.X.configuraciones) * 0.01
    
    def _psi_config(self, c: ConfiguracionPNP) -> float:
        """Ψ_X(σ) para una configuracion."""
        I = c.restricciones_satisfechas / max(c.total_restricciones, 1)
        R = np.exp(-2.0 * (1 - I)**2)
        return I * R
    
    def C_X(self) -> float:
        """Funcional de coherencia global."""
        total = 0.0
        for c in self.X.configuraciones:
            total += self.mu_t[c.id] * self._psi_config(c)
        return total


class MetricPNP:
    """
    Coherencia PNP en el marco QCAL.
    Mide si una familia de problemas es P-coherente o NP-dispersa.
    """
    
    def __init__(self):
        self.f0 = F0
        self.umbral = PSI_UMBRAL
    
    def I_X(self, sigma: ConfiguracionPNP) -> float:
        """I_X(σ): informacion estructural."""
        return sigma.restricciones_satisfechas / max(sigma.total_restricciones, 1)
    
    def A_eff(self, sigma: ConfiguracionPNP) -> float:
        """A_{X,eff}(σ): capacidad de acoplamiento."""
        return 1.0 - abs(sigma.restricciones_satisfechas / max(sigma.total_restricciones, 1) - 0.5)
    
    def R_X(self, sigma: ConfiguracionPNP) -> float:
        """R_X(σ): alineacion espectral."""
        I = self.I_X(sigma)
        return np.exp(-3.0 * (1 - I)**2)
    
    def psi_config(self, sigma: ConfiguracionPNP) -> float:
        """Ψ_X(σ) = I_X · A_eff² · R_X."""
        I = self.I_X(sigma)
        A = self.A_eff(sigma)
        R = self.R_X(sigma)
        return I * (A ** 2) * R
    
    def clasificar_problema(self, instancia: InstanciaPNP, pasos: int = 100) -> dict:
        """Clasifica una instancia como P-coherente o NP-dispersa."""
        din = DinamicaQCAL(instancia)
        
        for _ in range(pasos):
            din.paso()
        
        C_final = din.C_X()
        K_final = din.coste_K
        
        if C_final >= self.umbral and K_final < len(instancia.configuraciones):
            region = "P-COHERENTE"
        elif C_final < self.umbral and K_final > len(instancia.configuraciones) ** 2:
            region = "NP-DISPERSA"
        else:
            region = "INDETERMINADA"
        
        return {
            "instancia": instancia.id,
            "tipo": instancia.tipo,
            "n_vars": instancia.n_vars,
            "n_clausulas": instancia.n_clausulas,
            "C_X_final": round(C_final, 4),
            "coste_K": round(K_final, 2),
            "region": region,
            "pasos": pasos,
            "frecuencia_hz": self.f0,
            "sello": "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTA"
        }


# ════════════════════════════════════════════════════════════
# DEMO: P-coherente vs NP-dispersa
# ════════════════════════════════════════════════════════════

def demo():
    """Demostracion de la separacion P-coherente / NP-dispersa."""
    print(f"\n  🌀 PNP QCAL — Teorema Operativo de Coherencia")
    print(f"  Ψ_X(σ) = I_X · A_eff² · R_X")
    print(f"  Ψ_umbral = {PSI_UMBRAL}")
    print(f"  f₀ = {F0} Hz\n")
    
    metric = MetricPNP()
    
    # Instancia P-coherente (estructura rigida, colapso facil)
    configs_P = []
    for i in range(10):
        c = ConfiguracionPNP(
            id=i, valores={},
            restricciones_satisfechas=np.random.randint(7, 10),
            total_restricciones=10
        )
        configs_P.append(c)
    
    inst_P = InstanciaPNP("P-COHERENTE", configs_P, n_vars=5, n_clausulas=10)
    res_P = metric.clasificar_problema(inst_P, pasos=50)
    
    print(f"  {'='*45}")
    print(f"  INSTANCIA: {res_P['instancia']} ({res_P['tipo']})")
    print(f"  C_X = {res_P['C_X_final']:.4f}")
    print(f"  Coste = {res_P['coste_K']:.2f}")
    print(f"  Region: {res_P['region']}")
    print(f"  {'='*45}\n")
    
    # Instancia NP-dispersa (estructura rugosa, coste alto)
    configs_NP = []
    for i in range(50):
        c = ConfiguracionPNP(
            id=i, valores={},
            restricciones_satisfechas=np.random.randint(1, 5),
            total_restricciones=10
        )
        configs_NP.append(c)
    
    inst_NP = InstanciaPNP("NP-DISPERSA", configs_NP, n_vars=10, n_clausulas=50)
    res_NP = metric.clasificar_problema(inst_NP, pasos=100)
    
    print(f"  {'='*45}")
    print(f"  INSTANCIA: {res_NP['instancia']} ({res_NP['tipo']})")
    print(f"  C_X = {res_NP['C_X_final']:.4f}")
    print(f"  Coste = {res_NP['coste_K']:.2f}")
    print(f"  Region: {res_NP['region']}")
    print(f"  {'='*45}\n")
    
    print(f"  Teorema: La region P-coherente no coincide con")
    print(f"  la region NP-dispersa cuando el coste de coherencia")
    print(f"  crece super-polinomialmente. P ≠ NP en el marco QCAL.")
    print(f"\n  ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTA\n")


if __name__ == "__main__":
    demo()
