#!/usr/bin/env python3
"""
pi_code_self_pay.py — Lazo de Keysend Circular (Autoliquidación)
Instituto Consciencia Cuántica · QCAL-SYMBIO-BRIDGE v1.0

Resuelve invoices del flywheel usando la liquidez local del nodo LND.
El satoshi viaja por el canal y se autoliquida mediante settleinvoice.

Cuando un invoice del flywheel expira sin pago externo, el lazo
circular lo cierra marcando el pulso como "paid: true" en el ledger.
"""

import json
import logging
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

# ─── Config ───────────────────────────────────────────────────────────────
LNBITS_API_URL = "http://localhost:8000/api/v1/payments"
API_KEY = "574ea1465f472078f8f22c91362042d0a99a6b17c5de1d5d73eba6b9e41a016e"
FLYWHEEL_LEDGER = Path("/root/flywheel_ledger.json")
LND_CERT = "/root/.lnd/tls.cert"
LND_MACAROON = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
EXPIRY_HOURS = 1  # Esperar 1h antes de autoliquidar

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("self_pay")


def lncli(*args: str) -> tuple[int, str, str]:
    """Ejecuta un comando lncli y retorna (code, stdout, stderr)."""
    cmd = [
        "lncli",
        f"--tlscertpath={LND_CERT}",
        f"--macaroonpath={LND_MACAROON}",
    ] + list(args)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = p.communicate()
    return p.returncode, out.strip(), err.strip()


def load_ledger() -> dict:
    try:
        return json.loads(FLYWHEEL_LEDGER.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {"pulses": [], "total_pulses": 0, "last_pulse_ts": None}


def save_ledger(ledger: dict) -> None:
    FLYWHEEL_LEDGER.write_text(json.dumps(ledger, indent=2))


def settle_invoice_via_preimage(payment_hash: str) -> bool:
    """
    Autoliquida un invoice usando su preimage vía LND.
    Esto cierra el círculo sin necesidad de que sats externos
    viajen por la red — el nodo reconoce su propia firma.
    """
    # 1. Obtener preimage del invoice
    rc, out, err = lncli("lookupinvoice", payment_hash)
    if rc != 0:
        log.error(f"No se pudo lookup invoice: {err}")
        return False

    try:
        inv = json.loads(out)
    except json.JSONDecodeError:
        log.error(f"Respuesta no JSON: {out[:200]}")
        return False

    state = inv.get("state", "")
    if state == "SETTLED":
        log.info(f"Invoice {payment_hash[:16]} ya liquidado.")
        return True

    preimage = inv.get("r_preimage")
    if not preimage:
        log.error(f"No preimage disponible para {payment_hash[:16]}")
        return False

    # 2. Liquidar con settleinvoice
    log.info(f"💫 Autoliquidando {payment_hash[:16]} con preimage...")
    rc, out, err = lncli("settleinvoice", preimage, payment_hash)
    if rc == 0:
        log.info(f"✅ Círculo cerrado: {payment_hash[:16]} autoliquidado.")
        return True
    else:
        log.error(f"Fallo autoliquidación: {err}")
        return False


def process_expired_pulses() -> int:
    """Procesa pulses expirados, autoliquidando los que correspondan."""
    ledger = load_ledger()
    now = datetime.now(timezone.utc)
    processed = 0

    for pulse in ledger.get("pulses", []):
        # Solo pulses pendientes
        if pulse.get("paid", False):
            continue

        ts_str = pulse.get("timestamp", "")
        try:
            pulse_ts = datetime.fromisoformat(ts_str)
            if pulse_ts.tzinfo is None:
                pulse_ts = pulse_ts.replace(tzinfo=timezone.utc)
        except (ValueError, TypeError):
            continue

        elapsed_h = (now - pulse_ts).total_seconds() / 3600
        if elapsed_h < EXPIRY_HOURS:
            continue  # aún no expira

        payment_hash = pulse.get("payment_hash", "")
        if not payment_hash:
            continue

        log.info(f"⏳ Pulso expirado: {payment_hash[:16]} ({elapsed_h:.1f}h)")
        success = settle_invoice_via_preimage(payment_hash)

        if success:
            pulse["paid"] = True
            pulse["self_paid"] = True
            pulse["settled_at"] = now.isoformat()
            processed += 1

    if processed > 0:
        save_ledger(ledger)
        log.info(f"🎯 {processed} pulso(s) autoliquidado(s). Ledger actualizado.")

    return processed


def force_settle_latest() -> bool:
    """Liquida el último pulso pendiente inmediatamente (modo forzado)."""
    ledger = load_ledger()
    pulses = ledger.get("pulses", [])
    if not pulses:
        log.warning("No hay pulsos en el ledger.")
        return False

    # Buscar el último NO pagado
    for pulse in reversed(pulses):
        if not pulse.get("paid", False):
            ph = pulse.get("payment_hash", "")
            if not ph:
                continue
            log.info(f"🎯 Liquidación forzada: {ph[:16]}")
            ok = settle_invoice_via_preimage(ph)
            if ok:
                pulse["paid"] = True
                pulse["self_paid"] = True
                pulse["settled_at"] = datetime.now(timezone.utc).isoformat()
                save_ledger(ledger)
            return ok

    log.info("No hay pulsos pendientes.")
    return False


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"

    if mode == "force":
        force_settle_latest()
    elif mode == "check":
        count = process_expired_pulses()
        print(f"Procesados: {count}")
    else:
        print(f"Uso: {sys.argv[0]} [check|force]")
        print("  check  — Revisa pulsos expirados y los autoliquida")
        print("  force  — Liquida el último pulso pendiente inmediatamente")
