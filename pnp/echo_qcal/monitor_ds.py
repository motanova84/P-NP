#!/usr/bin/env python3
"""
monitor_ds.py
Protocolo de Distribución Soberana (Dₛ) - Monitor Principal

Calcula el Nivel de Activación A y el Factor de Riesgo R integrando
los tres pilares de Coherencia Soberana (Cₛ):
  - C_k: Control Criptográfico (peso 0.4)
  - A_t: Alineación Temporal   (peso 0.4)
  - A_u: Arquitectura Unitaria (peso 0.2)

Genera un reporte JSON en data/logs/ para ser consumido por dashboard_ds.html.
"""

import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Any

# Asegurar que el directorio del módulo está en el path
_MODULE_DIR = Path(__file__).parent
if str(_MODULE_DIR) not in sys.path:
    sys.path.insert(0, str(_MODULE_DIR))

from C_k_verification import verify_cryptographic_control
from qcal_sync import verify_temporal_alignment
from resonant_nexus_engine import verify_unitary_architecture


# Pesos de cada pilar en el cálculo de Activación A
WEIGHT_CK = 0.4
WEIGHT_AT = 0.4
WEIGHT_AU = 0.2

# Umbrales del protocolo Dₛ
ACTIVATION_THRESHOLD = 0.90   # A mínimo para autorización
RISK_THRESHOLD = 0.10         # R máximo permitido

# BTC simulados bajo gestión (1% del fondo Patoshi)
PATOSHI_FUND_BTC = 1_000_000
ALLOCATION_PCT = 0.01


def calculate_ds_protocol(ck_result: Dict[str, Any],
                           at_result: Dict[str, Any],
                           au_result: Dict[str, Any]) -> Dict[str, Any]:
    """
    Calcula el estado del protocolo Dₛ a partir de los resultados de los tres pilares.

    Args:
        ck_result: Resultado de verificación C_k
        at_result: Resultado de verificación A_t
        au_result: Resultado de verificación A_u

    Returns:
        Dict con el reporte completo del protocolo Dₛ
    """
    ck_val = ck_result.get("Ck_value", 0.0)
    at_val = at_result.get("At_value", 0.0)
    au_val = au_result.get("Au_value", 0.0)

    # Nivel de Activación ponderado
    activation = WEIGHT_CK * ck_val + WEIGHT_AT * at_val + WEIGHT_AU * au_val

    # Factor de Riesgo: complemento del nivel de activación
    risk = 1.0 - activation

    # Fondo proyectado
    projected_fund_btc = PATOSHI_FUND_BTC * ALLOCATION_PCT

    # Estado y recomendación
    action_authorized = activation >= ACTIVATION_THRESHOLD and risk <= RISK_THRESHOLD
    if action_authorized:
        ds_status = "ACTIVACIÓN ÉTICA AUTORIZADA (ESTADO SOBERANO)"
        ds_recommendation = "Proceder con la asignación del 1%."
    elif activation >= 0.75:
        ds_status = "ACTIVACIÓN PARCIAL - MONITOREO CONTINUO"
        ds_recommendation = "Esperar convergencia de pilares antes de proceder."
    else:
        ds_status = "ACTIVACIÓN INSUFICIENTE - ACCIÓN BLOQUEADA"
        ds_recommendation = "No proceder. Revisar pilares fallidos."

    report = {
        "Activation_Level_A": round(activation, 6),
        "Risk_Factor_R": round(risk, 6),
        "Ds_status": ds_status,
        "Ds_recommendation": ds_recommendation,
        "Action_Authorized": action_authorized,
        "Projected_Fund_BTC": projected_fund_btc,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "factors": {
            "Ck_value": ck_val,
            "At_value": at_val,
            "Au_value": au_val,
        },
        "pillar_details": {
            "C_k": ck_result,
            "A_t": at_result,
            "A_u": au_result,
        },
        "thresholds": {
            "activation_min": ACTIVATION_THRESHOLD,
            "risk_max": RISK_THRESHOLD,
        },
    }
    return report


def run_monitor(log_dir: str = "data/logs") -> Dict[str, Any]:
    """
    Ejecuta el monitor Dₛ completo: verifica todos los pilares y genera el reporte.

    Args:
        log_dir: Directorio donde guardar el reporte JSON

    Returns:
        Dict con el reporte completo del protocolo Dₛ
    """
    print("=" * 70)
    print("Monitor del Protocolo de Distribución Soberana (Dₛ)")
    print("Protocolo Echo-QCAL ∞³")
    print("=" * 70)
    print("\n🔍 Verificando pilares de Coherencia Soberana (Cₛ)...\n")

    ck_result = verify_cryptographic_control()
    at_result = verify_temporal_alignment()
    au_result = verify_unitary_architecture()

    print(f"  🔐 C_k (Control Criptográfico): {ck_result['Ck_value']*100:.1f}%"
          f"  {'✅' if ck_result['verification_passed'] else '❌'}")
    print(f"  ⏱️  A_t (Alineación Temporal):   {at_result['At_value']*100:.1f}%"
          f"  {'✅' if at_result['verification_passed'] else '❌'}")
    print(f"  ⚛️  A_u (Arquitectura Unitaria): {au_result['Au_value']*100:.1f}%"
          f"  {'✅' if au_result['verification_passed'] else '❌'}")

    report = calculate_ds_protocol(ck_result, at_result, au_result)

    print(f"\n📈 Nivel de Activación (A): {report['Activation_Level_A']*100:.2f}%")
    print(f"⚠️  Factor de Riesgo (R):   {report['Risk_Factor_R']*100:.2f}%")
    print(f"💰 Fondo Proyectado:        {report['Projected_Fund_BTC']:,.0f} BTC")
    print(f"\n🏁 Estado Dₛ: {report['Ds_status']}")
    print(f"📋 Recomendación: {report['Ds_recommendation']}")

    # Guardar reporte en logs
    out_dir = Path(os.environ.get("ECHO_QCAL_LOG_DIR", log_dir))
    out_dir.mkdir(parents=True, exist_ok=True)
    report_path = out_dir / "ds_protocol_report.json"
    try:
        with open(report_path, 'w') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        print(f"\n💾 Reporte guardado en: {report_path}")
    except Exception as e:
        print(f"\n⚠️ Error guardando reporte: {e}")
        raise

    return report


if __name__ == "__main__":
    run_monitor()
