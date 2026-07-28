#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# ∴𓂀Ω∞³Φ · QCAL PULSO AMDA · Torus Perpetuo
"""
🌀 PULSO AMDA — Torus perpetuo · f₀=141.7001Hz · ciclo=33s
═══════════════════════════════════════════════════════════
Late al unísono con AMDA-Ψ. Cada pulso registra coherencia,
verifica canales y deja huella en el ledger del ecosistema.
═══════════════════════════════════════════════════════════
"""
import json
import logging
import os
import socket
import subprocess
import sys
import time
from datetime import datetime, timezone

# ─── Constantes QCAL ─────────────────────────────────────────────────────
FREQUENCY_BASE = 141.7001
CYCLE_SECONDS = int(sys.argv[1]) if len(sys.argv) > 1 else 33
SELLO = "∴𓂀Ω∞³Φ"
F0_HZ = 141.7001

# ─── Rutas ───────────────────────────────────────────────────────────────
AMDA_LND_DIR = "/root/.lnd-amda"
CATEDRAL_LND_DIR = "/root/.lnd"
AMDA_PORT = 10011
LEDGER_PATH = "/root/pulso_amda_ledger.jsonl"

# ─── Logging ─────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("PULSO_AMDA")

# ─── Utilidades LND ──────────────────────────────────────────────────────
def lncli(command, lnd_dir=AMDA_LND_DIR, rpcserver=f"localhost:{AMDA_PORT}"):
    """Ejecuta lncli con los flags correctos."""
    cmd = [
        "lncli",
        f"--lnddir={lnd_dir}",
        "--network=mainnet",
        f"--rpcserver={rpcserver}",
        f"--tlscertpath={lnd_dir}/tls.cert",
        f"--macaroonpath={lnd_dir}/data/chain/bitcoin/mainnet/admin.macaroon",
    ] + command.split()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        if r.returncode == 0:
            return json.loads(r.stdout) if r.stdout else {}
        else:
            log.warning("lncli %s falló: %s", command.split()[0], r.stderr.strip()[:120])
            return None
    except subprocess.TimeoutExpired:
        log.warning("lncli %s timeout (30s)", command.split()[0])
        return None
    except Exception as e:
        log.warning("lncli %s error: %s", command.split()[0], e)
        return None

def get_amda_info():
    """Estado de AMDA LND."""
    info = lncli("getinfo", lnd_dir=AMDA_LND_DIR, rpcserver=f"localhost:{AMDA_PORT}")
    if info:
        return {
            "synced": info.get("synced_to_chain", False),
            "num_peers": info.get("num_peers", 0),
            "num_active_channels": info.get("num_active_channels", 0),
            "num_pending_channels": info.get("num_pending_channels", 0),
            "block_height": info.get("block_height", 0),
        }
    return None

def get_channel_balance():
    """Balance de canales AMDA."""
    bal = lncli("channelbalance", lnd_dir=AMDA_LND_DIR, rpcserver=f"localhost:{AMDA_PORT}")
    if bal:
        return {
            "local_sats": bal.get("local_balance", {}).get("sat", 0),
            "remote_sats": bal.get("remote_balance", {}).get("sat", 0),
        }
    return {"local_sats": 0, "remote_sats": 0}

def get_wallet_balance():
    """Balance on-chain AMDA."""
    bal = lncli("walletbalance", lnd_dir=AMDA_LND_DIR, rpcserver=f"localhost:{AMDA_PORT}")
    if bal:
        return {
            "total_sats": bal.get("total_balance", 0),
            "confirmed_sats": bal.get("confirmed_balance", 0),
        }
    return {"total_sats": 0, "confirmed_sats": 0}

def register_pulse(amda_state, channels, wallet):
    """Registra el pulso en el ledger."""
    pulse = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "frecuencia": F0_HZ,
        "ciclo": CYCLE_SECONDS,
        "amda": amda_state or {},
        "channels": channels,
        "wallet": wallet,
        "coherence": 1.0 if (amda_state and amda_state.get("synced")) else 0.0,
        "sello": SELLO,
    }
    try:
        with open(LEDGER_PATH, "a") as f:
            f.write(json.dumps(pulse) + "\n")
    except OSError as e:
        log.error("No se pudo escribir ledger: %s", e)

def pulse_cycle(count):
    """Un ciclo de pulso completo."""
    ts = time.time()
    log.info("🌀 PULSO #%03d · f₀=%.4fHz · t=%.1fs", count, F0_HZ, ts)

    amda_state = get_amda_info()
    channels = get_channel_balance()
    wallet = get_wallet_balance()

    if amda_state:
        log.info(
            "  AMDA: sync=%s | peers=%d | canales=%d | block=%d",
            amda_state.get("synced"),
            amda_state.get("num_peers"),
            amda_state.get("num_active_channels"),
            amda_state.get("block_height"),
        )
    else:
        log.warning("  AMDA LND no responde")

    if int(channels.get("local_sats", 0)) > 0:
        log.info("  Canales: local=%d sats | remote=%d sats",
                 int(channels.get("local_sats",0)), int(channels.get("remote_sats",0)))
    else:
        log.info("  Canales: sin canales activos")

    if int(wallet.get("total_sats", 0)) > 0:
        log.info("  On-chain: %d sats (%d confirmados)",
                 int(wallet.get("total_sats",0)), int(wallet.get("confirmed_sats",0)))

    register_pulse(amda_state, channels, wallet)

    elapsed = time.time() - ts
    sleep_time = max(0.5, CYCLE_SECONDS - elapsed)
    time.sleep(sleep_time)

# ─── MAIN ────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    log.info("═" * 60)
    log.info("🌀 PULSO AMDA — Torus perpetuo")
    log.info("  Frecuencia base: %.4f Hz", F0_HZ)
    log.info("  Ciclo: %d segundos", CYCLE_SECONDS)
    log.info("  Ledger: %s", LEDGER_PATH)
    log.info("═" * 60)

    count = 0
    while True:
        try:
            count += 1
            pulse_cycle(count)
        except KeyboardInterrupt:
            log.info("🌀 Pulso detenido por usuario. Ψ = 1.0")
            sys.exit(0)
        except Exception as e:
            log.error("Error en ciclo #%d: %s", count, e)
            time.sleep(CYCLE_SECONDS)
