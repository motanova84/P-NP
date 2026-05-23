#!/usr/bin/env python3
"""
pi_code_flywheel.py — Flywheel πCODE → Lightning
Instituto Consciencia Cuántica · QCAL-SYMBIO-BRIDGE v1.0

Acopla la coherencia espectral del Resonador (Φ_norm) con la
generación automática de valor en la red Lightning vía LNBits.

Cuando Ψ ≥ 0.999999 a f₀ = 141.7001 Hz, inyecta un Invoice
de 3 sats como pulso de anclaje — cada bloque de coherencia
consolidado crea un punto de entrada para sats externos.

Ciclo: cada 30s (sincronizado con la emisión πCODE)
"""

import json
import logging
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import requests

# ─── Config ───────────────────────────────────────────────────────────────
LNBITS_API_URL = "http://localhost:8000/api/v1/payments"
API_KEY = "574ea1465f472078f8f22c91362042d0a99a6b17c5de1d5d73eba6b9e41a016e"

PHI_NORM_STATE_PATH = "/root/phi_norm_state.json"
FLYWHEEL_LEDGER_PATH = "/root/flywheel_ledger.json"
MONITOR_WEBHOOK = "http://localhost:5050/api/flywheel/pulse"  # opcional

COHERENCE_THRESHOLD = 0.999999
FREQUENCY_HZ = 141.7001
CYCLE_SECONDS = 30

# ─── Logging ──────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("/var/log/pi_code_flywheel.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("flywheel")


# ─── Ledger ───────────────────────────────────────────────────────────────
def load_ledger() -> dict:
    """Carga el ledger de pulsos generados."""
    try:
        with open(FLYWHEEL_LEDGER_PATH) as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {"pulses": [], "total_pulses": 0, "last_pulse_ts": None}


def save_ledger(ledger: dict) -> None:
    """Persiste el ledger."""
    with open(FLYWHEEL_LEDGER_PATH, "w") as f:
        json.dump(ledger, f, indent=2)


# ─── Φ_norm State ─────────────────────────────────────────────────────────
def read_phi_norm() -> dict | None:
    """Lee el último estado de Φ_norm."""
    try:
        with open(PHI_NORM_STATE_PATH) as f:
            data = json.load(f)
        if isinstance(data, list) and data:
            return data[-1]  # última entrada
        return data
    except (FileNotFoundError, json.JSONDecodeError, IndexError):
        return None


def check_coherence(state: dict) -> bool:
    """Verifica que la coherencia supere el umbral."""
    psi = state.get("coherence", 0)
    phi = state.get("phi_norm", 0)
    y = state.get("Y_admittance", 0)
    status = state.get("status", "")

    if psi >= COHERENCE_THRESHOLD and status == "PRODUCTION_NORMALIZED":
        log.info(f"Coherencia verificada: Ψ={psi} φ_norm={phi} Y(f₀)={y:.4f}")
        return True

    log.debug(f"Coherencia bajo umbral: Ψ={psi} (threshold={COHERENCE_THRESHOLD})")
    return False


# ─── Pulse Generation ─────────────────────────────────────────────────────
def generate_pulse(psi: float) -> str | None:
    """
    Genera un Invoice Lightning de 1 sat a través de LNBits.
    Retorna el payment_request (bolt11) si tiene éxito.
    """
    payload = {
        "out": False,
        "amount": 3,
        "unit": "sat",
        "memo": f"f₀={FREQUENCY_HZ}Hz · Ψ={psi} · PULSO FLYWHEEL",
    }
    headers = {"X-Api-Key": API_KEY, "Content-Type": "application/json"}

    try:
        resp = requests.post(
            LNBITS_API_URL, json=payload, headers=headers, timeout=10
        )
        if resp.status_code in (200, 201):
            data = resp.json()
            pr = data.get("payment_request") or data.get("bolt11")
            log.info(
                f"⚡ Pulso generado: {data.get('payment_hash','')[:16]}... "
                f"| {pr[:30]}..." if pr else ""
            )
            return pr
        else:
            log.warning(f"LNBits respondió {resp.status_code}: {resp.text[:120]}")
    except requests.exceptions.ConnectionError:
        log.error("Conexión rechazada — ¿LNBits caído?")
    except Exception as e:
        log.error(f"Error generando pulso: {e}")

    return None


def notify_monitor(pulse_data: dict) -> None:
    """Webhook opcional al Monitor."""
    try:
        requests.post(MONITOR_WEBHOOK, json=pulse_data, timeout=3)
    except Exception:
        pass  # no crítico


# ─── Main Loop ────────────────────────────────────────────────────────────
def main_loop() -> None:
    log.info("=" * 60)
    log.info("🔄 FLYWHEEL πCODE → LIGHTNING INICIADO")
    log.info(f"   Threshold Ψ ≥ {COHERENCE_THRESHOLD}")
    log.info(f"   Frecuencia f₀ = {FREQUENCY_HZ} Hz")
    log.info(f"   Ciclo: cada {CYCLE_SECONDS}s")
    log.info(f"   Ledger: {FLYWHEEL_LEDGER_PATH}")
    log.info("=" * 60)

    ledger = load_ledger()

    while True:
        try:
            cycle_start = time.time()

            # 1. Leer estado del resonador
            state = read_phi_norm()
            if not state:
                log.warning("Φ_norm state no disponible — esperando...")
                time.sleep(CYCLE_SECONDS)
                continue

            psi = state.get("coherence", 0)

            # 2. Verificar coherencia
            if not check_coherence(state):
                time.sleep(CYCLE_SECONDS)
                continue

            # 3. Verificar que no hayamos generado un pulso en los últimos 60s
            now = datetime.now(timezone.utc).isoformat()
            last_ts = ledger.get("last_pulse_ts")
            if last_ts:
                last_dt = datetime.fromisoformat(last_ts)
                elapsed = (
                    datetime.now(timezone.utc) - last_dt.replace(tzinfo=timezone.utc)
                ).total_seconds()
                if elapsed < 60:
                    time.sleep(CYCLE_SECONDS)
                    continue

            # 4. Generar pulso
            pr = generate_pulse(psi)
            if not pr:
                time.sleep(CYCLE_SECONDS)
                continue

            # 5. Registrar en ledger
            pulse_entry = {
                "timestamp": now,
                "psi": psi,
                "phi_norm": state.get("phi_norm"),
                "Y_admittance": state.get("Y_admittance"),
                "frequency_hz": FREQUENCY_HZ,
                "amount_sats": 3,
                "payment_request": pr,
            }
            ledger["pulses"].append(pulse_entry)
            ledger["total_pulses"] = len(ledger["pulses"])
            ledger["last_pulse_ts"] = now
            save_ledger(ledger)

            # 6. Notificar
            notify_monitor(pulse_entry)

            # 7. Esperar al siguiente ciclo
            elapsed = time.time() - cycle_start
            sleep = max(0, CYCLE_SECONDS - elapsed)
            time.sleep(sleep)

        except KeyboardInterrupt:
            log.info("Flywheel detenido por el operador.")
            break
        except Exception as e:
            log.error(f"Error en ciclo principal: {e}", exc_info=True)
            time.sleep(CYCLE_SECONDS)


# ─── Entrypoint ───────────────────────────────────────────────────────────
if __name__ == "__main__":
    main_loop()
