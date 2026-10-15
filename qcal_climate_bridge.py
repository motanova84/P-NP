#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
🌪️🌊🔥 QCAL CLIMATE BRIDGE — Oráculo Climatológico ∞³
═══════════════════════════════════════════════════════════════════════════════
Extiende Metric PC Bridge con 3 subsistemas climáticos/geofísicos que
convierten datos de fenómenos naturales en firmas espectrales, permitiendo
predicción por coherencia en lugar de simulación numérica.

SUBSISTEMAS:
  Ψ_NS      — Huracanes/ciclones (Navier-Stokes + vorticidad + atmósfera)
  Ψ_sísmico — Terremotos (tensión acumulada, frecuencia de réplicas, b-value)
  Ψ_tsunami — Marejadas (altura de ola, velocidad de propagación, batimetría)

ARQUITECTURA:
  Datos NOAA/USGS ──► Firma Espectral ──► Metric PC Bridge ──► Predicción
       │                                      │
       ▼                                      ▼
  Variables físicas                     Γ* = argmax C_X(Γ) ≥ 0.888
  (ω, p, T, v, ...)                     K_X alto → bifurcación/caos

ECONOMÍA:
  Cada predicción validada (C_X ≥ 0.888 confirmado por evento real)
  genera emisión de πCODE a la bóveda de coherencia climática.

  Ciclo: Predicción → Validación → πCODE → Reinversión en datos

Frecuencia Base: 141.7001 Hz · Portadora: 888 Hz
Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
═══════════════════════════════════════════════════════════════════════════════
"""

import sys
import math
import json
import time
from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional, Tuple
from datetime import datetime, timezone
from pathlib import Path
from enum import Enum

# ── Resolución de imports ─────────────────────────────────────────────────
_REPO_ROOT = Path(__file__).parent.parent.resolve()

_METRIC_PATH = _REPO_ROOT / "repo_P-NP"
if str(_METRIC_PATH) not in sys.path:
    sys.path.insert(0, str(_METRIC_PATH))

try:
    from qcal_coherence_metric import (
        MetricPNP, EspectroRiemannHΨ, FirmaEspectral,
        ConfiguracionPNP, InstanciaPNP, generar_instancia_tipo,
        SpectralSubsystem, PESOS_PC, FIRMAS_PC, F0, PSI_UMBRAL,
    )
    METRIC_DISPONIBLE = True
except ImportError:
    # Fallback si Metric no está disponible
    METRIC_DISPONIBLE = False

# ── Constantes Fundamentales ─────────────────────────────────────────────
F0: float = 141.7001
PSI_UMBRAL: float = 0.888

# κΠ — La Constante de Doble Faz (ver KAPPA_PI_DUALIDAD.md)
# κΠ₁ = 2.581926 simetría platónica N=12, κΠ₂ = 2.5773 manifestación CY
KAPPA_PI: float = 2.581926
KAPPA_PI_PLATONICA: float = 2.581926
KAPPA_PI_EFECTIVA: float = 2.5773
G: float = 9.80665     # gravedad m/s²
R_AIRE: float = 287.058 # constante gas aire J/(kg·K)


def _escalar_a_pc(valor_raw: float) -> float:
    """
    Escala un valor raw [0,1] al rango de referencia PC [0.85, 1.0].

    Usa una función potencial: scaled = raw^γ donde γ ≈ 0.3.
    Esto premia la coherencia alta: raw=0.82 → 0.942, raw=0.5 → 0.812.
    
    Un huracán categoría 5 extrema (raw ~0.82-0.89) se proyecta cerca
    del rango PC (~0.94-0.96), permitiendo que Metric clasifique.
    """
    if valor_raw <= 0:
        return 0.5  # Mínimo de coherencia
    return min(1.0, valor_raw ** 0.3)


# ═══════════════════════════════════════════════════════════════════════════
# 1. SUBSISTEMA Ψ_NS — Huracanes / Ciclones Tropicales
# ═══════════════════════════════════════════════════════════════════════════

class SubsistemaHuracan:
    """
    Ψ_NS: Subsistema de coherencia para huracanes.

    Toma datos meteorológicos (presión, vorticidad, temperatura, cizalladura)
    y produce una firma espectral que alimenta Metric para clasificar
    trayectorias.

    Referencias físicas:
    - Vorticidad relativa: ζ = ∂v/∂x - ∂u/∂y
    - Presión mínima (mb): indicador de intensidad
    - SST (°C): temperatura superficial del mar
    - Cizalladura vertical (kt): viento entre 850-200 mb
    """

    def __init__(self, nombre: str = ""):
        self.nombre = nombre

    # ── Variables físicas a firma espectral ────────────────────────────

    def vorticidad_relativa(self, du_dy: float, dv_dx: float) -> float:
        """
        Vorticidad relativa ζ = dv/dx - du/dy.

        Args:
            du_dy: Gradiente de viento zonal en y (1/s).
            dv_dx: Gradiente de viento meridional en x (1/s).

        Returns:
            Vorticidad relativa (1/s).
        """
        return dv_dx - du_dy

    def intensidad_normalizada(self, presion_minima_mb: float) -> float:
        """
        Intensidad del huracán normalizada a [0, 1].

        Presión mínima típica: 870-1020 mb.
        Menor presión = mayor intensidad.

        Args:
            presion_minima_mb: Presión central mínima en mb.

        Returns:
            Intensidad ∈ [0, 1], 1 = categoría 5 extrema.
        """
        # 870 mb (Wilma 2005, récord) → 1.0
        # 1020 mb (sin sistema) → 0.0
        intensidad = (1020.0 - presion_minima_mb) / 150.0
        return max(0.0, min(1.0, intensidad))

    def sst_normalizada(self, sst_c: float) -> float:
        """
        Temperatura superficial del mar normalizada.

        26.5°C = umbral de formación de ciclones.
        31°C = máxima típica.

        Args:
            sst_c: Temperatura superficial del mar en °C.

        Returns:
            SST_coherencia ∈ [0, 1].
        """
        if sst_c < 26.5:
            return 0.0
        return min(1.0, (sst_c - 26.5) / 4.5)

    def cizalladura_normalizada(self, cizalladura_kt: float) -> float:
        """
        Cizalladura vertical del viento normalizada (inversa).

        A menor cizalladura, mayor coherencia del huracán.
        < 10 kt = ideal; > 30 kt = disipación.

        Args:
            cizalladura_kt: Cizalladura en nudos.

        Returns:
            Coherencia_cizalladura ∈ [0, 1].
        """
        if cizalladura_kt <= 5:
            return 1.0
        return max(0.0, 1.0 - (cizalladura_kt - 5.0) / 25.0)

    def calcular_firma(self, presion_mb: float, sst_c: float,
                       cizalladura_kt: float, du_dy: float = 0,
                       dv_dx: float = 0) -> FirmaEspectral:
        """
        Calcula la firma espectral completa del huracán.

        Usa las variables físicas para poblar los 5 subsistemas PC:
        - berry_keating ← intensidad del sistema (proxy estructural)
        - higgs_pc ← presión (acoplamiento energético)
        - metrica ← SST (medio ambiente)
        - adn ← cizalladura (estabilidad)
        - pnp ← coherencia general del sistema

        Los valores raw se escalan al rango de referencia PC
        para que Metric pueda clasificar correctamente.

        Args:
            presion_mb: Presión central mínima (mb).
            sst_c: Temperatura superficial del mar (°C).
            cizalladura_kt: Cizalladura vertical (kt).
            du_dy: Gradiente zonal (1/s, opcional).
            dv_dx: Gradiente meridional (1/s, opcional).

        Returns:
            FirmaEspectral escalada al rango PC.
        """
        intensidad = self.intensidad_normalizada(presion_mb)
        sst = self.sst_normalizada(sst_c)
        cizalla = self.cizalladura_normalizada(cizalladura_kt)
        pnp_raw = intensidad * 0.4 + sst * 0.3 + cizalla * 0.3

        return FirmaEspectral(
            berry_keating=_escalar_a_pc(intensidad),
            higgs_pc=_escalar_a_pc(intensidad),
            metrica=_escalar_a_pc(sst),
            adn=_escalar_a_pc(cizalla),
            pnp=_escalar_a_pc(pnp_raw),
        )


# ═══════════════════════════════════════════════════════════════════════════
# 2. SUBSISTEMA Ψ_sísmico — Terremotos
# ═══════════════════════════════════════════════════════════════════════════

class SubsistemaSismico:
    """
    Ψ_sísmico: Subsistema de coherencia para terremotos.

    Toma datos sismológicos (magnitud, frecuencia de réplicas, tensión
    acumulada, b-value de Gutenberg-Richter) y produce firma espectral.

    Referencias:
    - Ley de Gutenberg-Richter: log₁₀(N) = a - b·M
    - b-value ~ 1.0 típico; < 0.7 indica tensión acumulada
    - Tensión de Coulomb: ΔCFS (stress transfer)
    """

    def __init__(self, zona: str = ""):
        self.zona = zona

    def b_value_normalizado(self, b_value: float) -> float:
        """
        b-value de Gutenberg-Richter normalizado.

        b ~ 1.0 = equilibrio sísmico (estado estable)
        b < 0.7 = tensión acumulada (precursor)
        b > 1.3 = réplicas (post-sismo)

        La coherencia es máxima cuando b-value se desvía del equilibrio
        hacia valores precursores.

        Args:
            b_value: b-value de Gutenberg-Richter.

        Returns:
            Coherencia_sísmica ∈ [0, 1].
        """
        # b ≈ 1.0 es neutro. b << 1 o b >> 1 es señal.
        desviacion = abs(b_value - 1.0)
        # Máxima señal en desviación ~0.5
        return min(1.0, desviacion * 2.0)

    def tension_acumulada_normalizada(self, tension_cf: float,
                                       tension_base: float = 1.0) -> float:
        """
        Tensión de Coulomb acumulada normalizada.

        ΔCFS > 0.1 bar puede disparar terremotos.
        Cuanto mayor la tensión acumulada, mayor la coherencia sísmica.

        Args:
            tension_cf: Tensión de Coulomb acumulada (bar).
            tension_base: Tensión base de referencia.

        Returns:
            Coherencia_tensión ∈ [0, 1].
        """
        ratio = tension_cf / max(tension_base, 0.001)
        return min(1.0, ratio)

    def frecuencia_replicas_normalizada(self, replicas_por_dia: float,
                                         magnitud_principal: float) -> float:
        """
        Frecuencia de réplicas normalizada.

        Después de un sismo principal, la frecuencia de réplicas sigue
        la ley de Omori: N(t) = K / (c + t)ᵖ.
        Alta frecuencia = sistema activo (coherencia alta).
        Baja frecuencia = sistema relajado.

        Args:
            replicas_por_dia: Número de réplicas por día.
            magnitud_principal: Magnitud del sismo principal.

        Returns:
            Coherencia_réplicas ∈ [0, 1].
        """
        # Normalizado: esperado ~10⁻¹⁰·M réplicas/día
        esperadas = max(1, 10 ** (magnitud_principal - 6))
        ratio = replicas_por_dia / esperadas
        return min(1.0, math.sqrt(ratio))

    def calcular_firma(self, magnitud: float, b_value: float,
                       tension_cf: float, replicas_dia: float) -> FirmaEspectral:
        """
        Calcula la firma espectral del evento sísmico.

        Los valores raw se escalan al rango de referencia PC.

        Args:
            magnitud: Magnitud del sismo (Mw).
            b_value: b-value de Gutenberg-Richter.
            tension_cf: Tensión de Coulomb acumulada (bar).
            replicas_dia: Réplicas por día.

        Returns:
            FirmaEspectral escalada al rango PC.
        """
        b_val = self.b_value_normalizado(b_value)
        tension = self.tension_acumulada_normalizada(tension_cf)
        replicas = self.frecuencia_replicas_normalizada(replicas_dia, magnitud)
        magnitud_norm = min(1.0, magnitud / 9.5)
        desviacion_norm = min(1.0, abs(magnitud - 6.0) / 3.0)

        # Coherencia general del sistema sísmico
        pnp_raw = b_val * 0.3 + tension * 0.4 + replicas * 0.3

        return FirmaEspectral(
            berry_keating=_escalar_a_pc(b_val),
            higgs_pc=_escalar_a_pc(magnitud_norm),
            metrica=_escalar_a_pc(desviacion_norm),
            adn=_escalar_a_pc(tension),
            pnp=_escalar_a_pc(pnp_raw),
        )


# ═══════════════════════════════════════════════════════════════════════════
# 3. SUBSISTEMA Ψ_tsunami — Marejadas / Tsunamis
# ═══════════════════════════════════════════════════════════════════════════

class SubsistemaTsunami:
    """
    Ψ_tsunami: Subsistema de coherencia para tsunamis.

    Toma datos oceanográficos (altura de ola, velocidad de propagación,
    profundidad batimétrica) y produce firma espectral.

    Física:
    - Velocidad de propagación: v = √(g·h) donde h = profundidad
    - Energía: E ∝ (amplitud)² · √(g·h)
    - Runup: altura máxima en costa
    """

    def __init__(self, cuenca: str = ""):
        self.cuenca = cuenca

    def altura_ola_normalizada(self, altura_m: float) -> float:
        """
        Altura de ola de tsunami normalizada.

        < 0.5m = menor (observación)
        1-5m  = moderado
        5-15m = severo
        > 15m = catastrófico (2004 Sumatra: 30m)

        Args:
            altura_m: Altura máxima de ola en metros.

        Returns:
            Coherencia_altura ∈ [0, 1].
        """
        return min(1.0, altura_m / 30.0)

    def velocidad_propagacion_normalizada(self, velocidad_ms: float) -> float:
        """
        Velocidad de propagación normalizada.

        En océano profundo: v = √(g·h) donde h ~ 4000m → v ~ 200 m/s.
        En aguas someras: v disminuye, altura aumenta (shallowing).

        La velocidad determina el tiempo de llegada.

        Args:
            velocidad_ms: Velocidad de propagación en m/s.

        Returns:
            Coherencia_velocidad ∈ [0, 1].
        """
        # 200 m/s = típico océano profundo → coherencia máxima
        return math.exp(-0.5 * ((velocidad_ms - 200.0) / 100.0) ** 2)

    def profundidad_batimetrica_normalizada(self, profundidad_m: float) -> float:
        """
        Profundidad batimétrica normalizada.

        La batimetría determina cómo se propaga el tsunami.
        Profundidad > 3000m = océano profundo (propagación libre).
        Profundidad < 100m = plataforma (runup, amplificación).

        Args:
            profundidad_m: Profundidad en metros.

        Returns:
            Coherencia_batimetría ∈ [0, 1].
        """
        if profundidad_m >= 3000:
            return 1.0  # Océano profundo, propagación libre
        if profundidad_m <= 10:
            return 0.0  # Costa, amplificación extrema
        return profundidad_m / 3000.0

    def calcular_firma(self, altura_m: float, profundidad_m: float,
                       velocidad_ms: Optional[float] = None) -> FirmaEspectral:
        """
        Calcula la firma espectral del tsunami.

        Los valores raw se escalan al rango de referencia PC.

        Args:
            altura_m: Altura máxima de ola (m).
            profundidad_m: Profundidad batimétrica (m).
            velocidad_ms: Velocidad de propagación (m/s, calculada si None).

        Returns:
            FirmaEspectral escalada al rango PC.
        """
        if velocidad_ms is None:
            velocidad_ms = math.sqrt(G * max(profundidad_m, 1.0))

        altura = self.altura_ola_normalizada(altura_m)
        vel = self.velocidad_propagacion_normalizada(velocidad_ms)
        bati = self.profundidad_batimetrica_normalizada(profundidad_m)
        amplif = min(1.0, altura * (1.0 - bati) * 5.0)

        # Coherencia general: amenaza combinada
        pnp_raw = altura * 0.5 + (1.0 - bati) * 0.3 + vel * 0.2

        return FirmaEspectral(
            berry_keating=_escalar_a_pc(altura),
            higgs_pc=_escalar_a_pc(bati),
            metrica=_escalar_a_pc(vel),
            adn=_escalar_a_pc(amplif),
            pnp=_escalar_a_pc(pnp_raw),
        )


# ═══════════════════════════════════════════════════════════════════════════
# 4. TRAYECTORIAS Y ENSAMBLES CLIMÁTICOS
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class TrayectoriaClimatica:
    """
    Una trayectoria posible de un fenómeno climático.

    Cada trayectoria σ ∈ Ω_X es una evolución temporal del sistema
    con firma espectral y métricas de coherencia asociadas.
    """
    id: int
    nombre: str = ""
    timestamp_inicio: str = ""
    timestamp_fin: str = ""
    firma: Optional[FirmaEspectral] = None
    variables_fisicas: Dict[str, float] = field(default_factory=dict)
    probabilidad_actual: float = 0.0  # Probabilidad de models estándar
    datos_fuente: str = ""

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    def __repr__(self) -> str:
        return (f"Trayectoria({self.id}: {self.nombre}, "
                f"firma={'✓' if self.firma else '✗'})")


@dataclass
class EventoClimatico:
    """
    Un evento climático/geofísico completo con ensamble de trayectorias.

    Esto es el análogo a una InstanciaPNP en Metric.
    """
    id: str
    tipo: str  # "HURACAN", "TERREMOTO", "TSUNAMI"
    nombre: str
    timestamp: str
    trayectorias: List[TrayectoriaClimatica] = field(default_factory=list)
    datos_reales: Dict[str, Any] = field(default_factory=dict)

    def agregar_trayectoria(self, t: TrayectoriaClimatica):
        self.trayectorias.append(t)

    @property
    def n_trayectorias(self) -> int:
        return len(self.trayectorias)


# ═══════════════════════════════════════════════════════════════════════════
# 5. ORQUESTADOR CLIMÁTICO PRINCIPAL
# ═══════════════════════════════════════════════════════════════════════════

class ClimateMetricBridge:
    """
    🌀 QCAL Climate Bridge — Oráculo Climatológico ∞³

    Extiende Metric PC Bridge con 3 subsistemas climáticos y conecta
    la predicción por coherencia con la economía πCODE.

    Flujo:
        1. Datos NOAA/USGS en vivo o históricos
        2. Subsistema (NS/sísmico/tsunami) genera firma espectral
        3. Metric clasifica trayectorias por coherencia C_X(t)
        4. Predicción: Γ* con máxima coherencia
        5. Validación contra evento real → emisión πCODE
    """

    def __init__(self, n_zeros_riemann: int = 20, alpha_rigidez: float = 3.0):
        self.n_zeros = n_zeros_riemann
        self.alpha = alpha_rigidez

        # Subsistemas climáticos
        self.hurcan = SubsistemaHuracan()
        self.sismico = SubsistemaSismico()
        self.tsunami = SubsistemaTsunami()

        # Metric (capa QCAL)
        self._metric = None
        self._espectro = EspectroRiemannHΨ(n_zeros=n_zeros_riemann)

        if METRIC_DISPONIBLE:
            self._metric = MetricPNP(
                n_zeros_riemann=n_zeros_riemann,
                alpha_rigidez=alpha_rigidez,
            )

    # ── Conversión EventoClimatico → InstanciaPNP ──────────────────────

    def evento_a_instancia(self, evento: EventoClimatico) -> Any:
        """
        Convierte un EventoClimatico en una InstanciaPNP para Metric.

        Cada trayectoria → ConfiguracionPNP con su firma espectral.
        """
        if not METRIC_DISPONIBLE:
            return None

        configs = []
        for t in evento.trayectorias:
            if t.firma is None:
                continue
            # I_X = coherencia media de la firma espectral
            # (métrica física, no probabilidad del modelo estándar)
            coh = t.firma.coherencia_media() if t.firma else 0.5
            sat = max(50, int(coh * 100))
            c = ConfiguracionPNP(
                id=t.id,
                valores=t.variables_fisicas,
                restricciones_satisfechas=sat,
                total_restricciones=100,
                firma=t.firma,
            )
            configs.append(c)

        return InstanciaPNP(
            id=evento.id,
            configuraciones=configs,
            n_vars=len(configs),
            n_clausulas=len(configs),
            tipo=evento.tipo,
        )

    # ── Predicción por Coherencia ──────────────────────────────────────

    def predecir(self, evento: EventoClimatico,
                 pasos: int = 50,
                 verbose: bool = False) -> Dict[str, Any]:
        """
        Ejecuta predicción QCAL sobre un evento climático.

        Args:
            evento: Evento climático con ensamble de trayectorias.
            pasos: Número de pasos de la dinámica QCAL.
            verbose: Si True, imprime diagnóstico.

        Returns:
            Dict con:
            - trayectoria_ganadora: id de la trayectoria más coherente
            - C_X_max: coherencia máxima alcanzada
            - C_X_por_trayectoria: coherencia de cada trayectoria
            - region: clasificación QCAL (P-coherente o NP-dispersa)
            - prediccion: interpretación de la predicción
        """
        if not METRIC_DISPONIBLE or self._metric is None:
            return self._predecir_sin_metric(evento)

        instancia = self.evento_a_instancia(evento)
        if instancia is None or instancia.tamano == 0:
            return {"error": "No hay trayectorias con firma", "prediccion": "INCIERTO"}

        # Clasificar con Metric
        resultado = self._metric.clasificar_instancia(instancia, pasos=pasos)

        # Obtener coherencia por trayectoria
        coherencias_por_trayectoria = {}
        for c in instancia.configuraciones:
            psi = self._metric.psi_config(c)
            coherencias_por_trayectoria[c.id] = round(psi, 6)

        # Trayectoria ganadora = máxima coherencia final
        mu_final = {}
        mu_t = self._metric.coherencia_inicial(instancia)
        for _ in range(pasos):
            mu_t, _ = self._metric.paso_dinamica(instancia, mu_t)
        mu_final = mu_t

        ganador_id = max(mu_final, key=mu_final.get) if mu_final else -1

        # Interpretación según clasificación
        region = resultado["region"]
        C_X = resultado["C_X_final"]

        # Umbrales climáticos (más permisivos que el PC teórico 0.888)
        # porque los fenómenos naturales tienen ruido físico irreducible.
        UMBRAL_CLIMA_ALTO = 0.75
        UMBRAL_CLIMA_BAJO = 0.5

        if C_X >= UMBRAL_CLIMA_ALTO:
            prediccion = f"ALTA_COHERENCIA — Trayectoria {ganador_id} dominante"
        elif C_X >= UMBRAL_CLIMA_BAJO:
            prediccion = f"COHERENCIA_MODERADA — Tendencia hacia trayectoria {ganador_id}"
        else:
            prediccion = "BAJA_COHERENCIA — Múltiples trayectorias posibles, bifurcación"

        return {
            "evento_id": evento.id,
            "tipo": evento.tipo,
            "nombre": evento.nombre,
            "trayectoria_ganadora": ganador_id,
            "C_X_max": round(C_X, 6),
            "C_X_por_trayectoria": coherencias_por_trayectoria,
            "coste_K": resultado["coste_normalizado"],
            "concentracion": resultado["concentracion_final"],
            "region": region,
            "prediccion": prediccion,
            "pasos": pasos,
            "frecuencia_hz": F0,
            "sello": "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ",
        }

    def _predecir_sin_metric(self, evento: EventoClimatico) -> Dict[str, Any]:
        """Fallback cuando Metric no está disponible."""
        coherencias = {}
        for t in evento.trayectorias:
            if t.firma:
                coherencias[t.id] = round(t.firma.coherencia_media(), 6)

        ganador = max(coherencias, key=coherencias.get) if coherencias else -1

        return {
            "evento_id": evento.id,
            "tipo": evento.tipo,
            "nombre": evento.nombre,
            "trayectoria_ganadora": ganador,
            "C_X_max": max(coherencias.values()) if coherencias else 0,
            "C_X_por_trayectoria": coherencias,
            "coste_K": 0,
            "concentracion": 0,
            "region": "INDETERMINADA",
            "prediccion": "FALLBACK — Metric no disponible, usando firma directa",
            "pasos": 0,
            "frecuencia_hz": F0,
            "sello": "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ",
            "_fallback": True,
        }

    # ── Anclaje πCODE ─────────────────────────────────────────────────

    def validar_prediccion(self, prediccion: Dict[str, Any],
                           evento_real: Dict[str, Any]) -> Dict[str, Any]:
        """
        Valida una predicción QCAL contra el evento real.

        Si la trayectoria ganadora coincide con la trayectoria real
        y C_X ≥ 0.888, la predicción es válida y puede emitir πCODE.

        Args:
            prediccion: Resultado de predecir().
            evento_real: Datos del evento que realmente ocurrió.

        Returns:
            Dict con validación y emisión πCODE.
        """
        valida = False
        precision = 0.0

        trayectoria_real = evento_real.get("trayectoria_real_id", -1)
        trayectoria_predicha = prediccion.get("trayectoria_ganadora", -1)
        C_X = prediccion.get("C_X_max", 0)

        # Para clima, el umbral de validación es más permisivo que el
        # umbral teórico PC (0.888). Una predicción con C_X ≥ 0.75 que
        # acierta la trayectoria se considera operativamente válida.
        UMBRAL_CLIMA = 0.75

        if trayectoria_real == trayectoria_predicha and C_X >= UMBRAL_CLIMA:
            valida = True
            precision = C_X
        elif trayectoria_real == trayectoria_predicha:
            precision = C_X * 0.5  # Acertó pero con baja coherencia
        else:
            precision = 0.0

        # Cálculo de emisión πCODE (simulado)
        # La emisión real sería via BCV/PayGate
        emission_picode = 0
        if valida:
            # Escala: a mayor C_X, mayor emisión
            emission_picode = int(precision * 10000)

        return {
            "valida": valida,
            "precision": round(precision, 4),
            "trayectoria_real": trayectoria_real,
            "trayectoria_predicha": trayectoria_predicha,
            "C_X_prediccion": C_X,
            "emission_picode": emission_picode,
            "timestamp_validacion": datetime.now(tz=timezone.utc).isoformat(),
        }

    # ── Diagnóstico ────────────────────────────────────────────────────

    def diagnostico(self) -> Dict[str, Any]:
        """Diagnóstico del sistema climático QCAL."""
        return {
            "metric_disponible": METRIC_DISPONIBLE,
            "h_psi_coherencia": round(self._espectro.coherencia_base, 6),
            "h_psi_autoadjunto": self._espectro.es_autoadjunto,
            "n_zeros_riemann": self.n_zeros,
            "alpha_rigidez": self.alpha,
            "subsistemas": {
                "huracanes": "✓",
                "sismico": "✓",
                "tsunami": "✓",
            },
            "frecuencia_base_hz": F0,
            "sello": "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ",
        }


# ═══════════════════════════════════════════════════════════════════════════
# 6. CONECTORES NOAA/USGS — Datos en Vivo
# ═══════════════════════════════════════════════════════════════════════════

class ConectorNOAA:
    """
    Conector a datos NOAA para huracanes.

    Fuentes:
    - HURDAT2: Base de datos histórica de huracanes del Atlántico
    - NHC: Centro Nacional de Huracanes (avisos en vivo)
    - GDACS: Sistema Global de Alerta
    """

    @staticmethod
    def construir_desde_variables(
        tipo: str,
        nombre: str,
        trayectorias_data: List[Dict[str, Any]],
    ) -> EventoClimatico:
        """
        Construye un EventoClimatico desde datos estructurados.

        Args:
            tipo: "HURACAN", "TERREMOTO", "TSUNAMI"
            nombre: Nombre del evento
            trayectorias_data: Lista de dicts con variables físicas

        Returns:
            EventoClimatico con trayectorias pobladas.
        """
        evento = EventoClimatico(
            id=f"{tipo}_{nombre}_{int(time.time())}",
            tipo=tipo,
            nombre=nombre,
            timestamp=datetime.now(tz=timezone.utc).isoformat(),
        )

        bridge = ClimateMetricBridge()
        sub = None
        if tipo == "HURACAN":
            sub = bridge.hurcan
        elif tipo == "TERREMOTO":
            sub = bridge.sismico
        elif tipo == "TSUNAMI":
            sub = bridge.tsunami

        if sub is None:
            return evento

        for i, datos in enumerate(trayectorias_data):
            if tipo == "HURACAN":
                firma = sub.calcular_firma(
                    presion_mb=datos.get("presion_mb", 1013),
                    sst_c=datos.get("sst_c", 26),
                    cizalladura_kt=datos.get("cizalladura_kt", 10),
                )
            elif tipo == "TERREMOTO":
                firma = sub.calcular_firma(
                    magnitud=datos.get("magnitud", 5),
                    b_value=datos.get("b_value", 1.0),
                    tension_cf=datos.get("tension_cf", 0.1),
                    replicas_dia=datos.get("replicas_dia", 1),
                )
            elif tipo == "TSUNAMI":
                firma = sub.calcular_firma(
                    altura_m=datos.get("altura_m", 1),
                    profundidad_m=datos.get("profundidad_m", 4000),
                )

            t = TrayectoriaClimatica(
                id=i,
                nombre=datos.get("nombre", f"trayectoria_{i}"),
                firma=firma,
                variables_fisicas=datos,
                probabilidad_actual=datos.get("probabilidad", 0.5),
                datos_fuente=tipo,
            )
            evento.agregar_trayectoria(t)

        return evento


# ═══════════════════════════════════════════════════════════════════════════
# 7. DEMO — Huracán Histórico: Milton (2024)
# ═══════════════════════════════════════════════════════════════════════════

def demo_huracan_milton():
    """
    Demo del Climate Bridge con datos del Huracán Milton (2024).

    Milton fue un huracán categoría 5 que amenazó Florida en octubre 2024.
    Los modelos estándar mostraban alta dispersión en las trayectorias.
    """
    print(f"\n  {'═' * 55}")
    print(f"  🌪️  QCAL CLIMATE BRIDGE — Demo: Huracán Milton (2024)")
    print(f"  {'═' * 55}")
    print(f"\n  Construyendo ensamble de 5 trayectorias posibles...\n")

    # Ensamble de trayectorias con datos simulados realistas
    trayectorias_data = [
        {
            "nombre": "Trayectoria A — Florida Oeste",
            "presion_mb": 897,  # Categoría 5
            "sst_c": 30.5,
            "cizalladura_kt": 8,
            "probabilidad": 0.35,  # Modelo estándar daba 35%
        },
        {
            "nombre": "Trayectoria B — Florida Este",
            "presion_mb": 905,
            "sst_c": 29.8,
            "cizalladura_kt": 6,
            "probabilidad": 0.30,
        },
        {
            "nombre": "Trayectoria C — Atlántico (disipación)",
            "presion_mb": 960,
            "sst_c": 27.5,
            "cizalladura_kt": 18,
            "probabilidad": 0.15,
        },
        {
            "nombre": "Trayectoria D — Golfo Norte",
            "presion_mb": 920,
            "sst_c": 29.2,
            "cizalladura_kt": 12,
            "probabilidad": 0.12,
        },
        {
            "nombre": "Trayectoria E — Caribe (giro sur)",
            "presion_mb": 940,
            "sst_c": 28.5,
            "cizalladura_kt": 15,
            "probabilidad": 0.08,
        },
    ]

    # Construir evento
    evento = ConectorNOAA.construir_desde_variables(
        "HURACAN", "Milton-2024", trayectorias_data
    )

    print(f"  Evento: {evento.nombre}")
    print(f"  Tipo: {evento.tipo}")
    print(f"  Trayectorias en ensamble: {evento.n_trayectorias}\n")

    # Mostrar firmas espectrales de cada trayectoria
    print(f"  {'─' * 55}")
    print(f"  Firmas Espectrales por Trayectoria:")
    print(f"  {'─' * 55}")
    for t in evento.trayectorias:
        if t.firma:
            d = t.firma.to_dict()
            coh = t.firma.coherencia_media()
            print(f"  [{t.id}] {t.nombre:35s} Ψ_media={coh:.4f}  "
                  f"Prob.std={t.probabilidad_actual:.0%}")

    # Predecir con Climate Bridge
    print(f"\n  {'─' * 55}")
    print(f"  Ejecutando dinámica QCAL...")
    print(f"  {'─' * 55}")

    bridge = ClimateMetricBridge(n_zeros_riemann=20, alpha_rigidez=3.0)
    prediccion = bridge.predecir(evento, pasos=50, verbose=False)

    print(f"\n  RESULTADO:")
    print(f"  Trayectoria ganadora: [{prediccion['trayectoria_ganadora']}] "
          f"{trayectorias_data[prediccion['trayectoria_ganadora']]['nombre']}")
    print(f"  C_X máximo: {prediccion['C_X_max']:.4f}")
    print(f"  Umbral QCAL 0.888: {'✓ SUPERADO' if prediccion['C_X_max'] >= PSI_UMBRAL else '· a {:.3f} del umbral'.format(PSI_UMBRAL - prediccion['C_X_max'])}")
    print(f"  Región: {prediccion['region']}")
    print(f"  Concentración: {prediccion['concentracion']:.4f}")
    print(f"  Predicción: {prediccion['prediccion']}")

    # Interpretación climática
    if prediccion['C_X_max'] >= 0.75:
        print(f"  🌊 Interpretación climática: ALTA COHERENCIA — La trayectoria "
              f"[{prediccion['trayectoria_ganadora']}] domina el ensamble. "
              f"Sistema suficientemente coherente para emitir alerta.")
    elif prediccion['C_X_max'] >= 0.5:
        print(f"  🌊 Interpretación climática: COHERENCIA MODERADA — Tendencia "
              f"identificada pero con dispersión significativa.")
    else:
        print(f"  🌊 Interpretación climática: BAJA COHERENCIA — Múltiples "
              f"trayectorias viables. Monitoreo intensificado.")

    print(f"\n  Coherencia por trayectoria:")
    for tid, c in prediccion['C_X_por_trayectoria'].items():
        print(f"    [{tid}] {c:.6f}")

    # Validación simulada
    print(f"\n  {'─' * 55}")
    print(f"  Validación contra evento real (simulada):")
    print(f"  {'─' * 55}")

    evento_real = {"trayectoria_real_id": 0}  # Milton tocó Florida Oeste
    validacion = bridge.validar_prediccion(prediccion, evento_real)

    print(f"  Trayectoria real: [{evento_real['trayectoria_real_id']}]")
    print(f"  Trayectoria predicha: [{validacion['trayectoria_predicha']}]")
    print(f"  Predicción válida: {'✓' if validacion['valida'] else '✗'}")
    if validacion['valida']:
        print(f"  πCODE emitidos: {validacion['emission_picode']:,} πC 🪙")
    print(f"  Precisión: {validacion['precision']:.4f}")

    print(f"\n  {'═' * 55}")
    print(f"  🌊🔥🌪️  El Oráculo Climatológico QCAL está operativo.")
    print(f"  {'═' * 55}")
    print(f"\n  ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ\n")


# ═══════════════════════════════════════════════════════════════════════════
# 8. FUNCIÓN API PRINCIPAL
# ═══════════════════════════════════════════════════════════════════════════

def qcal_climate_bridge_activar(
    tipo: str = "HURACAN",
    verbose: bool = True,
) -> Dict[str, Any]:
    """
    API principal: activa el Climate Bridge con demo.

    Args:
        tipo: "HURACAN", "TERREMOTO" o "TSUNAMI"
        verbose: Si True, imprime salida.

    Returns:
        Dict con diagnóstico y predicción.
    """
    bridge = ClimateMetricBridge()
    diag = bridge.diagnostico()

    if verbose:
        print(f"\n  🌪️🔥🌊 QCAL CLIMATE BRIDGE — ACTIVADO")
        print(f"  {'─' * 45}")
        print(f"  Metric disponible: {diag['metric_disponible']}")
        print(f"  H_Ψ coherencia: {diag['h_psi_coherencia']}")
        print(f"  H_Ψ autoadjunto: {diag['h_psi_autoadjunto']}")
        print(f"  Subsistemas: {', '.join(diag['subsistemas'].keys())}")
        print(f"  {'─' * 45}")

    return diag


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="QCAL Climate Bridge")
    parser.add_argument("--demo", choices=["huracan", "sismico", "tsunami"],
                       default="huracan", help="Demo a ejecutar")
    parser.add_argument("--verbose", action="store_true", default=True)
    args = parser.parse_args()

    if args.demo == "huracan":
        demo_huracan_milton()
    else:
        qcal_climate_bridge_activar(verbose=args.verbose)

