#!/usr/bin/env python3
"""
🌀 DISTRIBUIDOR AUTOMÁTICO DE DIVIDENDOS v2.0 — BAL-003
Ecosistema: πCODE / Trinity QCAL ∞³
═══════════════════════════════════════════════════════════════
Cuando sats externos entran a LND (vía PayGate, flywheel, etc.)
el distribuidor calcula y ejecuta la distribución proporcional
a las 6 wallets del ecosistema.

Capas:
  - Lightning: Keysend a wallets que soporten (0 fees, instantáneo)
  - On-chain:  PSBT batch para wallets Bitcoin (1 TX, ~3K sats fee)
═══════════════════════════════════════════════════════════════
Arquitecto: JMMB Ψ · Nodo: Noesis
f₀ = 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ
═══════════════════════════════════════════════════════════════
"""

import json
import logging
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from decimal import Decimal, ROUND_DOWN

# ─── Config ───────────────────────────────────────────────────────────────
LND_CERT = "/root/.lnd/tls.cert"
LND_MACAROON = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
DIVIDEND_LEDGER = Path("/root/dividend_ledger.json")
WALLETS_PATH = Path("/root/repo_P-NP/scripts/wallets_catedral.json")
THRESHOLD_SATS = 100       # Mínimo acumulado para distribuir
OPERATING_RESERVE = 500     # Sats que mantiene LND para fees
CHECK_INTERVAL = 300         # Cada 5 min

# Distribución de dividendos
DIVIDEND_SPLIT = {
    "Catedral Treasury": 0.50,  # 50% — hold estructural
    "JMMB":             0.23,  # 23% — Sustento + ICQ
    "AMDA":             0.08,  #  8%
    "Aurón":            0.08,  #  8%
    "Sophia":           0.06,  #  6%
    "Kairos":           0.05,  #  5%
}
# Total: 100%

# RECOMPRA — automantener a AMDA desde dividendo de JMMB
RECOMPRA_PCT = 0.10  # 10% del split de JMMB va a AMDA automaticamente
RECOMPRA_ORIGEN = "JMMB"
RECOMPRA_DESTINO = "AMDA"


# ─── Logging ──────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler("/var/log/dividend_distributor.log"),
              logging.StreamHandler()],
)
log = logging.getLogger("dividendos")


def lncli(*args: str) -> tuple[int, str, str]:
    cmd = ["lncli", f"--tlscertpath={LND_CERT}",
           f"--macaroonpath={LND_MACAROON}"] + list(args)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = p.communicate()
    return p.returncode, out.strip(), err.strip()


def get_lnd_balance() -> int:
    """Retorna el balance total de LND en sats."""
    rc, out, _ = lncli("walletbalance")
    if rc != 0:
        return 0
    try:
        return int(json.loads(out).get("total_balance", 0))
    except (json.JSONDecodeError, KeyError):
        return 0


def get_channel_balance() -> dict:
    """Retorna balance local y remoto de todos los canales."""
    rc, out, _ = lncli("listchannels")
    if rc != 0:
        return {"local": 0, "remote": 0}
    try:
        data = json.loads(out)
        local = sum(int(c.get("local_balance", "0")) for c in data.get("channels", []))
        remote = sum(int(c.get("remote_balance", "0")) for c in data.get("channels", []))
        return {"local": local, "remote": remote}
    except (json.JSONDecodeError, KeyError):
        return {"local": 0, "remote": 0}


def load_ledger() -> dict:
    try:
        return json.loads(DIVIDEND_LEDGER.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {
            "version": "QCAL-DIVIDEND-v2.0",
            "total_received": 0,
            "total_distributed": 0,
            "balance_pending": 0,
            "distributions": [],
            "wallet_totals": {name: 0 for name in DIVIDEND_SPLIT},
            "last_check": None,
        }


def save_ledger(ledger: dict) -> None:
    DIVIDEND_LEDGER.write_text(json.dumps(ledger, indent=2))


def calculate_distribution(new_sats: int) -> dict:
    """Calcula cuánto corresponde a cada wallet."""
    dist = {}
    for wallet, pct in DIVIDEND_SPLIT.items():
        # RECOMPRA: desde JMMB hacia AMDA
        if wallet == RECOMPRA_ORIGEN:
            pct_recompra = pct * RECOMPRA_PCT
            distribution[RECOMPRA_DESTINO]["sats"] += int(net_new * pct_recompra)
            pct -= pct_recompra  # restar lo que se redirige

        sats = int(new_sats * pct)
        if sats > 0:
            dist[wallet] = {"sats": sats, "pct": pct * 100}
    return dist


def distribute_onchain(distribution: dict) -> bool:
    """
    Distribuye vía on-chain (PSBT batch).
    Prepara una TX con múltiples outputs a las wallets destino.
    """
    # Por ahora, registramos la intención y logueamos
    log.info("=== DISTRIBUCIÓN ON-CHAIN ===")
    total = 0
    for wallet, info in distribution.items():
        log.info(f"  {wallet}: {info['sats']} sats ({info['pct']:.1f}%)")
        total += info["sats"]
    log.info(f"  Total: {total} sats · Fee estimado: ~3,000 sats")
    log.info("  (Requiere Ledger para firmar. PSBT pendiente.)")
    return True


def keysend_payment(node_pubkey: str, sats: int) -> bool:
    """Envía sats vía Keysend a un nodo Lightning específico."""
    if not node_pubkey or sats < 1:
        log.warning(f"Keysend ignorado: sin pubkey o sats insuficientes")
        return False
    rc, out, err = lncli("sendpayment", "--dest", node_pubkey,
                          "--amt", str(sats), "--keysend", "--force")
    if rc == 0:
        log.info(f"  ✅ Keysend {sats} sats → {node_pubkey[:16]}...")
        return True
    else:
        log.warning(f"  ❌ Keysend fallido: {err[:60]}")
        return False


def distribute_lightning(distribution: dict, node_map: dict) -> int:
    """Distribuye vía Lightning Keysend a los agentes que tengan nodo."""
    distributed = 0
    for wallet, info in distribution.items():
        npub = node_map.get(wallet, "")
        if npub:
            if keysend_payment(npub, info["sats"]):
                distributed += info["sats"]
        else:
            log.info(f"  ⏳ {wallet}: {info['sats']} sats (pendiente — sin nodo LN)")
    return distributed


def check_and_distribute() -> dict:
    """Ciclo principal: chequea balance, calcula, distribuye."""
    ledger = load_ledger()
    balance = get_lnd_balance()
    channels = get_channel_balance()
    total_liquid = balance + channels["local"]
    now = datetime.now(timezone.utc).isoformat()

    log.info(f"🔍 LND: {balance} sats wallet + {channels['local']} canales = {total_liquid} total")

    # Calcular nuevo valor recibido desde última verificación
    prev_total = ledger.get("total_received", 0)
    net_new = max(0, total_liquid - prev_total - OPERATING_RESERVE)

    if net_new < THRESHOLD_SATS:
        ledger["last_check"] = now
        save_ledger(ledger)
        log.info(f"  Sin nuevo valor significativo: {net_new} sats (umbral: {THRESHOLD_SATS})")
        return {"distributed": False, "net_new": net_new, "reason": "below_threshold"}

    # Hay valor nuevo para distribuir
    distribution = calculate_distribution(net_new)
    log.info(f"💰 Nuevos sats para distribuir: {net_new}")

    # Intentar distribución Lightning primero
    node_map = {}  # Aquí se registran los pubkeys LN de cada wallet cuando existan
    ln_distributed = distribute_lightning(distribution, node_map)
    onchain_pending = net_new - ln_distributed

    # Registrar en ledger
    dist_entry = {
        "timestamp": now,
        "total_sats": net_new,
        "lightning_distributed": ln_distributed,
        "onchain_pending": onchain_pending,
        "distribution": distribution,
        "balance_snapshot": {"wallet": balance, "channels": channels["local"]},
    }
    ledger["distributions"].append(dist_entry)
    ledger["total_received"] = total_liquid
    ledger["total_distributed"] += ln_distributed
    ledger["balance_pending"] = onchain_pending
    ledger["last_check"] = now

    # Actualizar totales por wallet
    for wallet, info in distribution.items():
        ledger["wallet_totals"][wallet] = \
            ledger["wallet_totals"].get(wallet, 0) + info["sats"]

    save_ledger(ledger)

    log.info(f"  ✅ Lightning: {ln_distributed} sats")
    log.info(f"  ⏳ On-chain: {onchain_pending} sats (requiere Ledger)")
    
    return {"distributed": True, "net_new": net_new,
            "lightning": ln_distributed, "onchain": onchain_pending}


def show_summary() -> None:
    """Muestra resumen del estado de dividendos."""
    ledger = load_ledger()
    balance = get_lnd_balance()
    
    print(f"\n╔═══ DIVIDENDOS QCAL ═══╗")
    print(f"║  Total recibido: {ledger['total_received']:>8} sats")
    print(f"║  Distribuido:    {ledger['total_distributed']:>8} sats ⚡")
    print(f"║  Pendiente (on-chain): {ledger['balance_pending']:>8} sats")
    print(f"║  LND wallet:     {balance:>8} sats")
    print(f"║  Distribuciones: {len(ledger['distributions'])}")
    print(f"╠══════════════════════════════════╣")
    for wallet, total in ledger.get("wallet_totals", {}).items():
        pct = DIVIDEND_SPLIT.get(wallet, 0) * 100
        print(f"║  {wallet:20s} {pct:5.1f}% → {total:>8} sats")
    print(f"╚══════════════════════════════════╝")


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "once"

    if mode == "daemon":
        log.info("🌀 Distribuidor de dividendos — MODO DAEMON")
        while True:
            try:
                check_and_distribute()
            except Exception as e:
                log.error(f"Error: {e}")
            time.sleep(CHECK_INTERVAL)

    elif mode == "once":
        result = check_and_distribute()
        print(json.dumps(result, indent=2))

    elif mode == "resumen":
        show_summary()

    elif mode == "fijar-pubkey":
        wallet = sys.argv[2]
        pubkey = sys.argv[3]
        print(f"Pubkey {pubkey[:16]}... asignada a {wallet}")
        print("(Implementar persistencia en próximo commit)")

    else:
        print(f"Uso: {sys.argv[0]} [daemon|once|resumen]")
        print("  daemon   — Bucle continuo cada 5 min")
        print("  once     — Una verificación")
        print("  resumen  — Estado actual")
