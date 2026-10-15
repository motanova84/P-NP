#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests de Coherencia para Metric QCAL PC Bridge.

Valida:
1. Importación de todos los módulos
2. Creación de instancias de prueba
3. Cálculo de Ψ_X(σ) = I_X · A_eff² · R_X
4. Dinámica QCAL (μ_t, C_X(t), K_X(t))
5. Clasificación P-coherente vs NP-dispersa
6. Orquestación del puente (Metric PC Bridge)

Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
Frecuencia: 141.7001 Hz
"""

import sys
import math
from pathlib import Path

_REPO_ROOT = Path(__file__).parent.parent.resolve()
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import pytest
import numpy as np

from qcal_coherence_metric import (
    MetricPNP, EspectroRiemannHΨ, FirmaEspectral,
    ConfiguracionPNP, InstanciaPNP, generar_instancia_tipo,
    SpectralSubsystem, PESOS_PC, FIRMAS_PC,
    F0, PSI_UMBRAL,
)

from metric_pc_bridge import MetricPCBridge, ReporteUnificado

# ─────────────────────────────────────────────────────────────────────────────
# 1. IMPORTACIÓN DE MÓDULOS
# ─────────────────────────────────────────────────────────────────────────────


def test_import_metric():
    """El módulo Metric debe importar sin errores."""
    from qcal_coherence_metric import (
        MetricPNP, EspectroRiemannHΨ, FirmaEspectral,
        ConfiguracionPNP, InstanciaPNP, generar_instancia_tipo,
        SpectralSubsystem, PESOS_PC, FIRMAS_PC,
        F0, PSI_UMBRAL,
    )
    assert F0 == 141.7001
    assert PSI_UMBRAL == 0.888
    assert SpectralSubsystem.BERRY_KEATING.value == "berry_keating"
    assert len(PESOS_PC) == 5
    assert abs(sum(PESOS_PC.values()) - 1.0) < 1e-6


def test_import_bridge():
    """El módulo Bridge debe importar sin errores."""
    from metric_pc_bridge import (
        MetricPCBridge, ReporteUnificado,
        CapaHΨ, CapaPC, CapaMetric,
        metric_pc_bridge_activar,
    )


# ─────────────────────────────────────────────────────────────────────────────
# 2. ESPECTRO H_Ψ
# ─────────────────────────────────────────────────────────────────────────────

def test_espectro_riemann():
    """H_Ψ debe proporcionar espectro y métricas de coherencia."""
    e = EspectroRiemannHΨ(n_zeros=10)
    assert e.es_autoadjunto == True
    assert 0.0 <= e.coherencia_base <= 1.0
    assert len(e.espectro) == 10
    assert all(v > 0 for v in e.espectro[:5])


def test_d_spec():
    """d_spec debe medir distancia espectral correctamente."""
    e = EspectroRiemannHΨ(n_zeros=10)

    # Firma perfecta (alineada con PC)
    firma_perfecta = {
        SpectralSubsystem.BERRY_KEATING: 0.95,
        SpectralSubsystem.HIGGS_PC: 0.95,
        SpectralSubsystem.METRICA: 0.94,
        SpectralSubsystem.ADN: 0.96,
        SpectralSubsystem.PNP: 0.94,
    }

    # Firma ruidosa
    firma_ruidosa = {
        SpectralSubsystem.BERRY_KEATING: 0.2,
        SpectralSubsystem.HIGGS_PC: 0.3,
        SpectralSubsystem.METRICA: 0.1,
        SpectralSubsystem.ADN: 0.2,
        SpectralSubsystem.PNP: 0.3,
    }

    dp = e.d_spec(firma_perfecta)
    dr = e.d_spec(firma_ruidosa)

    assert dp < dr, f"d_spec perfecta ({dp}) debe ser menor que ruidosa ({dr})"
    assert dp >= 0
    assert dr >= 0

    # R_X
    rp = e.factor_alineacion(firma_perfecta)
    rr = e.factor_alineacion(firma_ruidosa)
    assert rp > rr, f"R perfecta ({rp}) debe ser mayor que R ruidosa ({rr})"
    assert 0 < rp <= 1.0
    assert 0 < rr <= 1.0


# ─────────────────────────────────────────────────────────────────────────────
# 3. FIRMA ESPECTRAL Y CONFIGURACIONES
# ─────────────────────────────────────────────────────────────────────────────

def test_firma_espectral():
    """FirmaEspectral debe calcular coherencia media correctamente."""
    f = FirmaEspectral(0.95, 0.95, 0.94, 0.96, 0.94)
    media = f.coherencia_media()
    assert 0.9 < media < 1.0

    d = f.to_dict()
    assert len(d) == 5
    assert SpectralSubsystem.BERRY_KEATING in d


def test_configuracion_pnp():
    """ConfiguracionPNP debe calcular I_X correctamente."""
    c = ConfiguracionPNP(id=0, restricciones_satisfechas=8, total_restricciones=10)
    assert c.I_X == 0.8

    c2 = ConfiguracionPNP(id=1, restricciones_satisfechas=0, total_restricciones=0)
    assert c2.I_X == 0.0


def test_instancia_pnp():
    """InstanciaPNP debe identificar soluciones."""
    configs = [
        ConfiguracionPNP(0, restricciones_satisfechas=10, total_restricciones=10),
        ConfiguracionPNP(1, restricciones_satisfechas=5, total_restricciones=10),
        ConfiguracionPNP(2, restricciones_satisfechas=10, total_restricciones=10),
    ]
    inst = InstanciaPNP("TEST", configs, n_vars=3, n_clausulas=10)
    assert inst.tamano == 3
    assert len(inst.soluciones) == 2


# ─────────────────────────────────────────────────────────────────────────────
# 4. MÉTRICA PNP
# ─────────────────────────────────────────────────────────────────────────────

def test_metric_pnp_components():
    """Las componentes I_X, A_eff, R_X deben producir Ψ en [0,1]."""
    m = MetricPNP(n_zeros_riemann=10)

    c_perfecta = ConfiguracionPNP(
        0, restricciones_satisfechas=10, total_restricciones=10,
        firma=FirmaEspectral(0.95, 0.95, 0.94, 0.96, 0.94),
    )
    c_ruidosa = ConfiguracionPNP(
        1, restricciones_satisfechas=2, total_restricciones=10,
        firma=FirmaEspectral(0.2, 0.3, 0.1, 0.2, 0.3),
    )

    # Componentes
    assert m.I_X(c_perfecta) > m.I_X(c_ruidosa)
    assert m.A_eff(c_perfecta) > m.A_eff(c_ruidosa)
    assert m.R_X(c_perfecta) > m.R_X(c_ruidosa)

    # Ψ final
    psi_p = m.psi_config(c_perfecta)
    psi_r = m.psi_config(c_ruidosa)
    assert psi_p > psi_r
    assert 0 <= psi_p <= 1.0
    assert 0 <= psi_r <= 1.0


def test_dinamica_qcal():
    """La dinámica QCAL debe concentrar coherencia en soluciones."""
    m = MetricPNP(n_zeros_riemann=10)
    inst = generar_instancia_tipo("TEST", 10, "P-COHERENTE", n_soluciones=2)

    mu_0 = m.coherencia_inicial(inst)
    assert abs(sum(mu_0.values()) - 1.0) < 1e-6

    # Un paso de dinámica
    mu_1, coste = m.paso_dinamica(inst, mu_0)
    assert abs(sum(mu_1.values()) - 1.0) < 1e-6
    assert coste >= 0

    # C_X debe aumentar
    C_0 = m.C_X(inst, mu_0)
    C_1 = m.C_X(inst, mu_1)
    assert C_1 >= C_0, "C_X debe aumentar o mantenerse"


def test_clasificacion():
    """La clasificación debe separar P-coherente de NP-dispersa."""
    m = MetricPNP(n_zeros_riemann=10)

    # P-COHERENTE
    inst_p = generar_instancia_tipo("P-TEST", 10, "P-COHERENTE", n_soluciones=2)
    res_p = m.clasificar_instancia(inst_p, pasos=30)
    assert res_p["region"] in ("P-COHERENTE", "INDETERMINADA"), \
        f"P-COHERENTE dio {res_p['region']}"
    assert res_p["C_X_final"] >= 0.5

    # NP-DISPERSA
    inst_np = generar_instancia_tipo("NP-TEST", 30, "NP-DISPERSA")
    res_np = m.clasificar_instancia(inst_np, pasos=50)
    assert res_np["region"] == "NP-DISPERSA", \
        f"NP-DISPERSA dio {res_np['region']}"
    assert res_np["C_X_final"] < 0.5


# ─────────────────────────────────────────────────────────────────────────────
# 5. GENERACIÓN DE INSTANCIAS
# ─────────────────────────────────────────────────────────────────────────────

def test_generar_instancias():
    """Los 3 tipos de instancia deben generarse correctamente."""
    for tipo, n, nsol in [("P-COHERENTE", 10, 2), ("NP-DISPERSA", 30, 0),
                          ("INDETERMINADA", 15, 3)]:
        inst = generar_instancia_tipo(tipo, n_configs=n, tipo=tipo, n_soluciones=nsol)
        assert len(inst.configuraciones) == n
        assert inst.tipo == tipo
        assert inst.n_vars > 0


# ─────────────────────────────────────────────────────────────────────────────
# 6. BRIDGE — ORQUESTADOR
# ─────────────────────────────────────────────────────────────────────────────

def test_bridge_diagnostico():
    """El bridge debe diagnosticar las 3 capas."""
    from metric_pc_bridge import MetricPCBridge
    bridge = MetricPCBridge(n_zeros_riemann=10)
    diag = bridge.diagnostico_rapido()
    assert "H_Ψ" in diag
    assert "PC" in diag
    assert "METRIC" in diag
    for estado in diag.values():
        assert len(estado) > 0


def test_bridge_reporte():
    """El bridge debe generar reporte unificado con las 3 capas."""
    from metric_pc_bridge import MetricPCBridge
    bridge = MetricPCBridge(n_zeros_riemann=10)
    reporte = bridge.analisis_completo()
    capas = reporte.a_dict()

    assert "capa_h_psi" in capas
    assert "capa_pc" in capas
    assert "capa_metric" in capas
    assert "timestamp" in capas
    assert "sello" in capas

    # H_Ψ
    h = capas["capa_h_psi"]
    assert "es_autoadjunto" in h
    assert "coherencia_cuantica" in h

    # PC
    pc = capas["capa_pc"]
    assert "psi_global" in pc
    assert "subsistemas" in pc

    # Metric
    m = capas["capa_metric"]
    assert "resultados" in m
    assert "P-COHERENTE" in m["resultados"]


# ─────────────────────────────────────────────────────────────────────────────
# 7. CONSTANTES E INVARIANTES
# ─────────────────────────────────────────────────────────────────────────────

def test_constantes_fundamentales():
    """Las constantes fundamentales deben ser consistentes.
    κΠ dual: κΠ₁ = 2.581926 (platónico N=12), κΠ₂ = 2.5773 (efectivo CY)
    """
    from qcal_coherence_metric import (
        F0, PSI_UMBRAL, KAPPA_PI,
        KAPPA_PI_PLATONICA, KAPPA_PI_EFECTIVA,
    )
    import math
    phi = (1 + math.sqrt(5)) / 2
    kappa_expected = math.log(12) / math.log(phi ** 2)
    assert F0 == 141.7001
    assert PSI_UMBRAL == 0.888
    # κΠ₁ — simetría platónica
    assert abs(KAPPA_PI - kappa_expected) < 1e-6
    assert abs(KAPPA_PI_PLATONICA - 2.581926) < 1e-4
    # κΠ₂ — manifestación efectiva (Calabi-Yau)
    assert abs(KAPPA_PI_EFECTIVA - 2.5773) < 1e-4
    # La diferencia entre ambas = 1/216 ≈ 0.00463 (6³, dimensiones compactas)
    dif = abs(KAPPA_PI_PLATONICA - KAPPA_PI_EFECTIVA)
    assert abs(dif - 0.004626) < 0.001, f"Diferencia κΠ₁−κΠ₂ = {dif} debe ser ≈ 0.004626"


def test_subsistemas_pc():
    """Los 5 subsistemas PC deben tener coherencias en [0,1]."""
    for nombre, valor in FIRMAS_PC.items():
        assert 0 <= valor <= 1.0, f"{nombre}: {valor} fuera de rango"
    assert FIRMAS_PC[SpectralSubsystem.PNP] >= PSI_UMBRAL


def test_pesos_normalizados():
    """Los pesos de la PC deben sumar 1."""
    assert abs(sum(PESOS_PC.values()) - 1.0) < 1e-6


# ─────────────────────────────────────────────────────────────────────────────
# 8. CASOS LÍMITE
# ─────────────────────────────────────────────────────────────────────────────

def test_configuracion_cero():
    """Configuración con restricciones cero debe ser manejable."""
    m = MetricPNP(n_zeros_riemann=10)
    c = ConfiguracionPNP(0, restricciones_satisfechas=0, total_restricciones=0)
    assert m.I_X(c) == 0.0
    psi = m.psi_config(c)
    assert psi == 0.0


def test_instancia_vacia():
    """Instancia sin configuraciones no debe fallar."""
    inst = InstanciaPNP("EMPTY", [], n_vars=0, n_clausulas=0)
    assert inst.tamano == 0
    assert len(inst.soluciones) == 0


def test_entropia_uniforme():
    """Distribución uniforme debe tener entropía-normalizada = 0."""
    m = MetricPNP(n_zeros_riemann=10)
    configs = [ConfiguracionPNP(i) for i in range(5)]
    inst = InstanciaPNP("H-UNIF", configs, n_vars=2, n_clausulas=5)
    mu = m.coherencia_inicial(inst)
    H = m.entropia_medida(mu)
    assert abs(H) < 0.01, f"Entropía uniforme debe ser ~0, dio {H}"


def test_entropia_concentrada():
    """Distribución concentrada debe tener entropía-normalizada = 1."""
    m = MetricPNP(n_zeros_riemann=10)
    mu = {0: 0.999, 1: 0.001, 2: 0.0}
    H = m.entropia_medida(mu)
    assert H > 0.95, f"Entropía concentrada debe ser ~1, dio {H}"
