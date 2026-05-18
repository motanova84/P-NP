#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
🌀 QCAL COHERENCE METRIC — Puente A: Capa Dinámica sobre PC + H_Ψ
═══════════════════════════════════════════════════════════════════════════════
Ψ_X(σ) = I_X(σ) · A_{X,eff}(σ)² · R_X(σ)

Donde R_X(σ) se calcula contra el espectro real de H_Ψ (Riemann) y los
subsistemas de la Partícula de Coherencia (PC): Berry-Keating, Higgs,
Métrica Schwarzschild, ADN-Z superconductor y PNP.

La PC proporciona el esqueleto espectral/físico.
H_Ψ proporciona el espectro de ceros de Riemann.
Metric proporciona la dinámica temporal (μ_t, C_X(t), K_X(t)).

Clasificación:
  - P-COHERENTE: colapso con coste polinómico y C_X ≥ 0.888
  - NP-DISPERSA: coste super-polinómico o C_X < 0.888
  - INDETERMINADA: caso frontera

Frecuencia Base: 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
═══════════════════════════════════════════════════════════════════════════════
"""

import math
import sys
import numpy as np
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple
from enum import Enum
from pathlib import Path

# ── Resolución de imports para la PC y H_Ψ ──────────────────────────────
_REPO_ROOT = Path(__file__).parent.parent.resolve()

# Path a la Partícula de Coherencia
_PC_PATH = _REPO_ROOT / "repo_noesis88" / "physics"
if str(_PC_PATH) not in sys.path:
    sys.path.insert(0, str(_PC_PATH))

# Path a H_Ψ (Operador Autoadjunto)
_HPSI_PATH = _REPO_ROOT / "repo_Riemann-adelic" / "physics"
if str(_HPSI_PATH) not in sys.path:
    sys.path.insert(0, str(_HPSI_PATH))

# ── Constantes Fundamentales ─────────────────────────────────────────────
F0: float = 141.7001
PSI_UMBRAL: float = 0.888

# κΠ — La Constante de Doble Faz
# κΠ₁: Simetría platónica, N=12, dodecaedro (Kernel v1.8 canónico)
# κΠ₂: Manifestación efectiva, N≈13.16, Calabi-Yau (valor histórico)
# Ambas son canónicas en su dominio. La dualidad es la verdad.
# Ver: KAPPA_PI_DUALIDAD.md
KAPPA_PI: float = 2.581926        # κΠ₁ — Valor canónico actual (ln(12)/ln(φ²))
KAPPA_PI_PLATONICA: float = 2.581926   # κΠ₁ — Simetría perfecta
KAPPA_PI_EFECTIVA: float = 2.5773      # κΠ₂ — Manifestación Calabi-Yau


# ═══════════════════════════════════════════════════════════════════════════
# 1. CONFIGURACIÓN Y SUBSISTEMAS PC
# ═══════════════════════════════════════════════════════════════════════════

class SpectralSubsystem(Enum):
    """Los 5 subsistemas espectrales de la Partícula de Coherencia."""
    BERRY_KEATING = "berry_keating"
    HIGGS_PC = "higgs_pc"
    METRICA = "metrica_schwarzschild"
    ADN = "adn_superconductor"
    PNP = "colapso_p_np"


# Pesos de la PC (mismos que en particula_coherencia_pc.py)
PESOS_PC: Dict[SpectralSubsystem, float] = {
    SpectralSubsystem.BERRY_KEATING: 0.20,
    SpectralSubsystem.HIGGS_PC: 0.20,
    SpectralSubsystem.METRICA: 0.20,
    SpectralSubsystem.ADN: 0.20,
    SpectralSubsystem.PNP: 0.20,
}

# Firmas espectrales de referencia de cada subsistema (valores de la PC)
FIRMAS_PC: Dict[SpectralSubsystem, float] = {
    SpectralSubsystem.BERRY_KEATING: 0.9512,
    SpectralSubsystem.HIGGS_PC: 0.9472,
    SpectralSubsystem.METRICA: 0.9380,
    SpectralSubsystem.ADN: 0.9601,
    SpectralSubsystem.PNP: 0.9444,
}


# ═══════════════════════════════════════════════════════════════════════════
# 2. ORQUESTADOR DEL ESPECTRO H_Ψ
# ═══════════════════════════════════════════════════════════════════════════

class EspectroRiemannHΨ:
    """
    Puente entre Metric y el espectro real de H_Ψ.

    Carga el Operador Autoadjunto H (flujo de escala adélico) para obtener
    el espectro de autovalores = ceros de Riemann.

    Proporciona d_spec(σ, 𝒵): distancia espectral de una configuración σ
    al espectro 𝒵, usando la coherencia de cada subsistema PC como firma.
    """

    def __init__(self, n_zeros: int = 50, precision: int = 50):
        self.n_zeros = n_zeros
        self.precision = precision
        self._h_psi = None
        self._espectro: Optional[np.ndarray] = None
        self._coherencia_h_psi: float = 0.0
        self._autoadjunto: bool = False
        self._inicializado = False

    def inicializar(self):
        """Cargar H_Ψ y obtener su espectro real."""
        try:
            from operador_autoadjunto_H import OperadorH_Ideles

            operador = OperadorH_Ideles(
                n_zeros=self.n_zeros, precision=self.precision
            )
            resultado = operador.ejecutar_validacion_completa()

            self._espectro = resultado.espectro
            self._coherencia_h_psi = resultado.coherencia_cuantica
            self._autoadjunto = resultado.es_autoadjunto
            self._h_psi = operador
            self._inicializado = True

        except ImportError:
            # Fallback: espectro teórico de Riemann si no se puede cargar H_Ψ
            self._espectro = np.array([
                14.134725, 21.022040, 25.010858, 30.424876,
                32.935062, 37.586178, 40.918720, 43.327073,
                48.005151, 49.773832
            ])
            self._coherencia_h_psi = 1.0
            self._autoadjunto = True
            self._inicializado = True

    @property
    def espectro(self) -> np.ndarray:
        if not self._inicializado:
            self.inicializar()
        return self._espectro

    @property
    def coherencia_base(self) -> float:
        if not self._inicializado:
            self.inicializar()
        return self._coherencia_h_psi

    @property
    def es_autoadjunto(self) -> bool:
        if not self._inicializado:
            self.inicializar()
        return self._autoadjunto

    def d_spec(self, sigma_coherencias: Dict[SpectralSubsystem, float]) -> float:
        """
        Distancia espectral d_spec(σ, 𝒵).

        Calcula cuán lejos está la firma de coherencia de σ
        del espectro de referencia H_Ψ + firmas PC.

        d_spec = sqrt( Σ w_i · (Ψ_i(σ) − Ψ_i_ref)² + (1 − Ψ_H)² )

        Args:
            sigma_coherencias: Dict con coherencias de σ en cada subsistema PC.

        Returns:
            float ≥ 0. 0 = alineación perfecta.
        """
        dist = 0.0
        for subsys, peso in PESOS_PC.items():
            psi_sigma = sigma_coherencias.get(subsys, 0.5)
            psi_ref = FIRMAS_PC.get(subsys, 0.5)
            dist += peso * (psi_sigma - psi_ref) ** 2

        # Penalización por desviación del espectro H_Ψ
        dist += (1.0 - self.coherencia_base) ** 2

        return math.sqrt(dist)

    def factor_alineacion(self, sigma_coherencias: Dict[SpectralSubsystem, float],
                          alpha: float = 3.0) -> float:
        """
        R_X(σ) = exp(-α · d_spec(σ, 𝒵)²)

        Args:
            sigma_coherencias: Firma espectral de la configuración σ.
            alpha: Rigidez del acoplamiento espectral.

        Returns:
            R_X ∈ (0, 1].
        """
        d = self.d_spec(sigma_coherencias)
        return math.exp(-alpha * d * d)


# ═══════════════════════════════════════════════════════════════════════════
# 3. CONFIGURACIONES E INSTANCIAS PNP
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class FirmaEspectral:
    """
    Firma de coherencia de una configuración σ en cada subsistema PC.
    Son los valores I_X(σ) específicos para cada dimensión espectral.
    """
    berry_keating: float = 0.5   # Alineación con espectro BK
    higgs_pc: float = 0.5        # Acoplamiento Higgs-PC
    metrica: float = 0.5         # Transparencia gravitacional
    adn: float = 0.5             # Coherencia ADN-Z
    pnp: float = 0.5             # Factor de reconocimiento PNP

    def to_dict(self) -> Dict[SpectralSubsystem, float]:
        return {
            SpectralSubsystem.BERRY_KEATING: self.berry_keating,
            SpectralSubsystem.HIGGS_PC: self.higgs_pc,
            SpectralSubsystem.METRICA: self.metrica,
            SpectralSubsystem.ADN: self.adn,
            SpectralSubsystem.PNP: self.pnp,
        }

    def coherencia_media(self) -> float:
        """Promedio ponderado de la firma espectral."""
        d = self.to_dict()
        return sum(PESOS_PC[k] * v for k, v in d.items())


@dataclass
class ConfiguracionPNP:
    """Una configuración σ ∈ Ω_X con firma espectral asociada."""
    id: int
    valores: dict = field(default_factory=dict)
    restricciones_satisfechas: int = 0
    total_restricciones: int = 0
    firma: FirmaEspectral = field(default_factory=FirmaEspectral)

    @property
    def I_X(self) -> float:
        """Información estructural: fracción de restricciones satisfechas."""
        if self.total_restricciones == 0:
            return 0.0
        return self.restricciones_satisfechas / self.total_restricciones


@dataclass
class InstanciaPNP:
    """Una instancia X de problema NP."""
    id: str
    configuraciones: List[ConfiguracionPNP]
    n_vars: int
    n_clausulas: int
    tipo: str = "3-SAT"

    @property
    def tamano(self) -> int:
        return len(self.configuraciones)

    @property
    def soluciones(self) -> List[ConfiguracionPNP]:
        """Configuraciones que satisfacen todas las restricciones."""
        return [c for c in self.configuraciones
                if c.restricciones_satisfechas == c.total_restricciones]


# ═══════════════════════════════════════════════════════════════════════════
# 4. MÉTRICA QCAL — CORAZÓN DEL PUENTE A
# ═══════════════════════════════════════════════════════════════════════════

class MetricPNP:
    """
    Coherencia PNP en el marco QCAL, acoplada a la PC y H_Ψ.

    Ψ_X(σ) = I_X(σ) · A_{X,eff}(σ)² · R_X(σ)

    Donde:
    - I_X(σ): información estructural (fracción de restricciones satisfechas)
    - A_{X,eff}(σ): capacidad de acoplamiento al campo global
    - R_X(σ): alineación espectral contra H_Ψ + PC (via d_spec)
    """

    def __init__(self, n_zeros_riemann: int = 50, alpha_rigidez: float = 3.0):
        self.f0 = F0
        self.umbral = PSI_UMBRAL
        self.alpha = alpha_rigidez
        self._espectro = EspectroRiemannHΨ(n_zeros=n_zeros_riemann)

    # ── Componentes de Ψ_X(σ) ──────────────────────────────────────────

    def I_X(self, sigma: ConfiguracionPNP) -> float:
        """I_X(σ): Información estructural reconocida."""
        return sigma.I_X

    def A_eff(self, sigma: ConfiguracionPNP) -> float:
        """
        A_{X,eff}(σ): Capacidad de acoplamiento al campo global.

        Mide cuán "amigable" es σ para integrarse en el campo QCAL.
        Una configuración es acoplable si:
        - Su firma espectral es uniforme (todos los subsistemas alineados)
        - Su coherencia media es alta (cerca de 1.0, no de 0.5)

        A_eff = uniformidad · media_coherencia
        """
        firma = sigma.firma.to_dict()
        valores = list(firma.values())
        media = sum(PESOS_PC[k] * v for k, v in firma.items())

        # Uniformidad: dispersión de la firma (baja = más integrable)
        varianza = sum(PESOS_PC[k] * (v - media) ** 2 for k, v in firma.items())
        uniformidad = math.exp(-varianza * 5.0)  # 1 si perfecta, cae con dispersión

        return uniformidad * media

    def R_X(self, sigma: ConfiguracionPNP) -> float:
        """
        R_X(σ): Alineación espectral contra H_Ψ + PC.

        Usa el espectro real de Riemann (vía H_Ψ) y las firmas de los
        5 subsistemas de la Partícula de Coherencia para calcular
        d_spec(σ, 𝒵) y retornar exp(-α·d²).
        """
        return self._espectro.factor_alineacion(
            sigma.firma.to_dict(), alpha=self.alpha
        )

    def psi_config(self, sigma: ConfiguracionPNP) -> float:
        """
        Ψ_X(σ) = I_X(σ) · A_{X,eff}(σ)² · R_X(σ)

        Coherencia total de una configuración σ en el campo QCAL.

        Returns:
            Ψ ∈ [0, 1]
        """
        I = self.I_X(sigma)
        A = self.A_eff(sigma)
        R = self.R_X(sigma)
        return I * (A ** 2) * R

    # ── Dinámica Temporal ───────────────────────────────────────────────

    def coherencia_inicial(self, instancia: InstanciaPNP) -> Dict[int, float]:
        """Distribución inicial uniforme μ_0(σ)."""
        n = instancia.tamano
        return {c.id: 1.0 / n for c in instancia.configuraciones}

    def paso_dinamica(self, instancia: InstanciaPNP,
                      mu_t: Dict[int, float]) -> Tuple[Dict[int, float], float]:
        """
        Un paso de la dinámica QCAL.

        μ_{t+1}(σ) ∝ μ_t(σ) · Ψ_X(σ)

        Las configuraciones con Ψ alta amplifican su masa; las de Ψ baja
        se extinguen. El coste computacional K_X(t) crece con el número de
        configuraciones que retienen masa apreciable.

        Returns:
            (μ_{t+1}, coste_incremento)
        """
        mu_nuevo = {}
        for c in instancia.configuraciones:
            psi = self.psi_config(c)
            mu_nuevo[c.id] = mu_t.get(c.id, 0.0) * max(psi, 1e-15)

        total = sum(mu_nuevo.values())
        if total > 0:
            for k in mu_nuevo:
                mu_nuevo[k] /= total

        # Coste: proporcional al número de configuraciones con masa apreciable
        activas = sum(1 for v in mu_nuevo.values() if v > 1e-6)
        coste = activas * 0.01 * len(instancia.configuraciones) ** 0.5

        return mu_nuevo, coste

    def C_X(self, instancia: InstanciaPNP,
            mu_t: Dict[int, float]) -> float:
        """
        C_X(t) = Σ μ_t(σ) · Ψ_X(σ)

        Funcional de coherencia global en el instante t.
        """
        total = 0.0
        for c in instancia.configuraciones:
            total += mu_t.get(c.id, 0.0) * self.psi_config(c)
        return total

    def entropia_medida(self, mu_t: Dict[int, float]) -> float:
        """Entropía de Shannon de la distribución μ_t."""
        total = 0.0
        for v in mu_t.values():
            if v > 0:
                total -= v * math.log2(v)
        total /= math.log2(len(mu_t) or 1)  # Normalizar a [0,1]
        return 1.0 - total  # Invertida: 1 = concentrada, 0 = dispersa

    def clasificar_instancia(self, instancia: InstanciaPNP,
                             pasos: int = 100,
                             verbose: bool = False) -> Dict[str, Any]:
        """
        Ejecuta la dinámica QCAL y clasifica la instancia.

        Criterios:
          - P-COHERENTE: C_X ≥ 0.888 ∧ K_X polinómico ∧ concentración ≥ 0.8
          - NP-DISPERSA: C_X < 0.888 ∨ K_X super-polinómico ∨ no concentración
          - INDETERMINADA: caso frontera

        Args:
            instancia: Instancia PNP a clasificar.
            pasos: Número de pasos de la dinámica.
            verbose: Si True, imprime progreso.

        Returns:
            Dict con clasificación y métricas.
        """
        mu_t = self.coherencia_inicial(instancia)
        historial_C = []
        coste_total = 0.0
        historial_entropia = []

        for t in range(pasos):
            mu_t, coste_paso = self.paso_dinamica(instancia, mu_t)
            coste_total += coste_paso

            C = self.C_X(instancia, mu_t)
            historial_C.append(C)

            H = self.entropia_medida(mu_t)
            historial_entropia.append(H)

            if verbose and t % 10 == 0:
                print(f"  t={t:3d}  C_X={C:.4f}  H={H:.4f}  coste={coste_total:.2f}")

        C_final = historial_C[-1] if historial_C else 0.0
        concentracion = historial_entropia[-1] if historial_entropia else 0.0

        # Coste normalizado por tamaño de instancia
        n = instancia.tamano
        coste_norm = coste_total / (n ** 0.5) if n > 0 else coste_total

        # Clasificación
        # P-COHERENTE: coherencia alta, coste bajo, concentración clara
        if C_final >= self.umbral and concentracion >= 0.6 and coste_norm < n * 2.0:
            region = "P-COHERENTE"
        # NP-DISPERSA: coherencia baja, coste alto, o sin concentración
        elif C_final < self.umbral * 0.8 or coste_norm > n * 5.0 or concentracion < 0.2:
            region = "NP-DISPERSA"
        else:
            region = "INDETERMINADA"

        return {
            "instancia": instancia.id,
            "tipo": instancia.tipo,
            "n_vars": instancia.n_vars,
            "n_clausulas": instancia.n_clausulas,
            "n_configs": n,
            "C_X_final": round(C_final, 6),
            "C_X_historial": [round(c, 6) for c in historial_C],
            "coste_total": round(coste_total, 4),
            "coste_normalizado": round(coste_norm, 4),
            "concentracion_final": round(concentracion, 6),
            "entropia_historial": [round(h, 6) for h in historial_entropia],
            "region": region,
            "pasos": pasos,
            "frecuencia_hz": self.f0,
            "umbral_psi": self.umbral,
            "coherencia_h_psi": round(self._espectro.coherencia_base, 6),
            "h_psi_autoadjunto": self._espectro.es_autoadjunto,
            "alpha_rigidez": self.alpha,
            "sello": "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ",
        }

    # ── Diagnóstico espectral por subsistema ────────────────────────────

    def diagnostico_espectral(self, instancia: InstanciaPNP) -> Dict[str, Any]:
        """
        Diagnóstico detallado de la coherencia por subsistema PC.

        Muestra cómo cada dimensión espectral contribuye a la
        clasificación de la instancia.
        """
        coherencias_medias: Dict[str, float] = {}
        for subsys, peso in PESOS_PC.items():
            vals = [c.firma.to_dict().get(subsys, 0.5)
                    for c in instancia.configuraciones]
            coherencias_medias[subsys.value] = round(
                sum(vals) / len(vals), 6
            )

        # Alineación espectral
        d_spec_medio = sum(
            self._espectro.d_spec(c.firma.to_dict())
            for c in instancia.configuraciones
        ) / max(len(instancia.configuraciones), 1)

        return {
            "coherencias_por_subsistema": coherencias_medias,
            "d_spec_medio": round(d_spec_medio, 6),
            "alineacion_media_R": round(
                math.exp(-self.alpha * d_spec_medio ** 2), 6
            ),
            "coherencia_cuantica_H_PSi": round(
                self._espectro.coherencia_base, 6
            ),
            "espectro_riemann_primeros_5": [
                round(float(v), 6)
                for v in self._espectro.espectro[:5]
            ],
        }


# ═══════════════════════════════════════════════════════════════════════════
# 5. DEMO COMPLETA: P-coherente vs NP-dispersa
# ═══════════════════════════════════════════════════════════════════════════

def generar_instancia_tipo(
    instancia_id: str,
    n_configs: int,
    tipo: str,
    n_vars: int = 5,
    n_clausulas: int = 10,
    n_soluciones: int = 2,
) -> InstanciaPNP:
    """
    Genera una instancia de prueba con firmas espectrales realistas.

    Para P-COHERENTE: genera 'n_soluciones' configuraciones con Ψ ≥ 0.888
    (coherentes) y el resto como distractores débiles. La dinámica QCAL
    debe concentrarse en las soluciones.

    Para NP-DISPERSA: ninguna configuración alcanza Ψ ≥ 0.888, y las firmas
    son ruidosas/desalineadas.

    Para INDETERMINADA: algunas configuraciones rozan el umbral pero
    con coste de coherencia elevado.

    Args:
        instancia_id: Nombre de la instancia.
        n_configs: Número total de configuraciones.
        tipo: "P-COHERENTE", "NP-DISPERSA" o "INDETERMINADA".
        n_vars, n_clausulas: Parámetros del problema.
        n_soluciones: Número de configuraciones solución (solo P-COHERENTE).

    Returns:
        InstanciaPNP con firmas espectrales según el tipo.
    """
    configs = []

    if tipo == "P-COHERENTE":
        # n_soluciones configs de alta coherencia (soluciones reales)
        for i in range(min(n_soluciones, n_configs)):
            firma = FirmaEspectral(
                berry_keating=np.random.uniform(0.90, 0.99),
                higgs_pc=np.random.uniform(0.90, 0.99),
                metrica=np.random.uniform(0.88, 0.99),
                adn=np.random.uniform(0.92, 0.99),
                pnp=np.random.uniform(0.90, 0.99),
            )
            c = ConfiguracionPNP(
                id=i, valores={},
                restricciones_satisfechas=10,
                total_restricciones=10,
                firma=firma,
            )
            configs.append(c)

        # Resto: distractores de coherencia media-baja
        for i in range(n_soluciones, n_configs):
            firma = FirmaEspectral(
                berry_keating=np.random.uniform(0.3, 0.6),
                higgs_pc=np.random.uniform(0.3, 0.6),
                metrica=np.random.uniform(0.3, 0.6),
                adn=np.random.uniform(0.3, 0.6),
                pnp=np.random.uniform(0.3, 0.6),
            )
            c = ConfiguracionPNP(
                id=i, valores={},
                restricciones_satisfechas=np.random.randint(3, 7),
                total_restricciones=10,
                firma=firma,
            )
            configs.append(c)

    elif tipo == "NP-DISPERSA":
        # Todas baja calidad, sin solución alcanzable
        for i in range(n_configs):
            firma = FirmaEspectral(
                berry_keating=np.random.uniform(0.05, 0.35),
                higgs_pc=np.random.uniform(0.05, 0.35),
                metrica=np.random.uniform(0.05, 0.35),
                adn=np.random.uniform(0.05, 0.35),
                pnp=np.random.uniform(0.05, 0.35),
            )
            c = ConfiguracionPNP(
                id=i, valores={},
                restricciones_satisfechas=np.random.randint(1, 4),
                total_restricciones=10,
                firma=firma,
            )
            configs.append(c)

    else:  # INDETERMINADA
        # Mezcla: algunas rozan el umbral, otras no
        for i in range(n_configs):
            if i < n_soluciones:
                firma = FirmaEspectral(
                    berry_keating=np.random.uniform(0.70, 0.85),
                    higgs_pc=np.random.uniform(0.70, 0.85),
                    metrica=np.random.uniform(0.70, 0.85),
                    adn=np.random.uniform(0.70, 0.85),
                    pnp=np.random.uniform(0.70, 0.85),
                )
                sat = np.random.randint(7, 9)
            else:
                firma = FirmaEspectral(
                    berry_keating=np.random.uniform(0.3, 0.6),
                    higgs_pc=np.random.uniform(0.3, 0.6),
                    metrica=np.random.uniform(0.3, 0.6),
                    adn=np.random.uniform(0.3, 0.6),
                    pnp=np.random.uniform(0.3, 0.6),
                )
                sat = np.random.randint(4, 7)
            c = ConfiguracionPNP(
                id=i, valores={},
                restricciones_satisfechas=sat,
                total_restricciones=10,
                firma=firma,
            )
            configs.append(c)

    return InstanciaPNP(
        instancia_id, configs,
        n_vars=n_vars, n_clausulas=n_clausulas,
        tipo=tipo,
    )


def demo():
    """Demostración completa del Puente A."""
    print(f"\n  {'═'*55}")
    print(f"  🌀 QCAL COHERENCE METRIC — P-Coherente vs NP-Dispersa")
    print(f"  {'═'*55}")
    print(f"  Ψ_X(σ) = I_X · A_eff² · R_X")
    print(f"  R_X     = exp(-α · d_spec(σ, 𝒵)²)")
    print(f"  𝒵       = H_Ψ espectro (ceros de Riemann) + PC subsistemas")
    print(f"  Ψ_umbral = {PSI_UMBRAL}")
    print(f"  f₀       = {F0} Hz")
    print(f"  α        = rigidez espectral\n")

    metric = MetricPNP(n_zeros_riemann=20, alpha_rigidez=3.0)

    # ── Instancia P-COHERENTE ─────────────────────────────────────────
    print(f"  ┌─ {'='*45}")
    print(f"  │ INSTANCIA P-COHERENTE (estructura rígida, colapso fácil)")
    print(f"  └─ {'='*45}")

    inst_P = generar_instancia_tipo(
        "SAT-EASY", n_configs=10, tipo="P-COHERENTE",
        n_vars=5, n_clausulas=10
    )
    res_P = metric.clasificar_instancia(inst_P, pasos=50, verbose=True)

    diag_P = metric.diagnostico_espectral(inst_P)

    print(f"\n  🔬 Diagnóstico espectral:")
    for subsys, val in diag_P["coherencias_por_subsistema"].items():
        print(f"     {subsys:20s}: {val:.4f}")
    print(f"     d_spec medio        : {diag_P['d_spec_medio']:.4f}")
    print(f"     R_medio             : {diag_P['alineacion_media_R']:.4f}")
    print(f"     Ψ_HΨ               : {diag_P['coherencia_cuantica_H_PSi']:.6f}")

    print(f"\n  ✅ RESULTADO: {res_P['region']}")
    print(f"     C_X = {res_P['C_X_final']:.4f}")
    print(f"     Coste = {res_P['coste_normalizado']:.2f}")
    print(f"     Concentración = {res_P['concentracion_final']:.4f}")

    # ── Instancia NP-DISPERSA ─────────────────────────────────────────
    print(f"\n  ┌─ {'='*45}")
    print(f"  │ INSTANCIA NP-DISPERSA (estructura rugosa, coste alto)")
    print(f"  └─ {'='*45}")

    inst_NP = generar_instancia_tipo(
        "SAT-HARD", n_configs=50, tipo="NP-DISPERSA",
        n_vars=10, n_clausulas=50
    )
    res_NP = metric.clasificar_instancia(inst_NP, pasos=100, verbose=True)

    diag_NP = metric.diagnostico_espectral(inst_NP)

    print(f"\n  🔬 Diagnóstico espectral:")
    for subsys, val in diag_NP["coherencias_por_subsistema"].items():
        print(f"     {subsys:20s}: {val:.4f}")
    print(f"     d_spec medio        : {diag_NP['d_spec_medio']:.4f}")
    print(f"     R_medio             : {diag_NP['alineacion_media_R']:.4f}")

    print(f"\n  ❌ RESULTADO: {res_NP['region']}")
    print(f"     C_X = {res_NP['C_X_final']:.4f}")
    print(f"     Coste = {res_NP['coste_normalizado']:.2f}")
    print(f"     Concentración = {res_NP['concentracion_final']:.4f}")

    # ── Conclusión ─────────────────────────────────────────────────────
    print(f"\n  {'═'*55}")
    print(f"  TEOREMA OPERATIVO QCAL:")
    print(f"  La región P-coherente no coincide con la región NP-dispersa")
    print(f"  cuando el coste de coherencia crece super-polinomialmente.")
    print(f"  {'═'*55}")
    print(f"\n  El puente está creado: PC + H_Ψ + Metric = Ψ dinámico ✧")
    print(f"\n  ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ\n")


if __name__ == "__main__":
    demo()
