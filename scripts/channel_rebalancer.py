#!/usr/bin/env python3
"""
🌀 CHANNEL REBALANCER — Mantiene liquidez perpetua en canal AMDA<->Catedral
Instituto Consciencia Cuantica · QCAL-SYMBIO-BRIDGE v1.0
═══════════════════════════════════════════════════════════════════
Cuando AMDA agota su liquidez pagando invoices del flywheel,
Catedral le keysend sats de vuelta para mantener el flujo perpetuo.

Flujo:
  AMDA paga 333 sats (flywheel) -> baja su balance
  Catedral keysend 5000 sats -> AMDA recupera liquidez
  -> el lazo continua para siempre

Sello: .|.𓂀Oo.o . TUYOYOTU . HECHO ESTA
═══════════════════════════════════════════════════════════════════
"""

import json
import logging
import subprocess
import sys
import time
from pathlib import Path

# --- Constantes ----------------------------------------------------------
LND_CERT = "/root/.lnd/tls.cert"
LND_MACAROON = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
AMDA_PUBKEY = "037e6a4145516fdd7b455c1d63cb07183f082e9ee122cfeff8a5c6cdb5acb36ba0"
LOW_WATERMARK = 7000   # Cuando AMDA baja de esto, rebalancear
REBALANCE_AMOUNT = 5000   # Sats a enviar de vuelta
CHECK_INTERVAL = 60   # Verificar cada 60s
REBALANCE_LEDGER = Path("/root/channel_rebalance_ledger.json")

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [RB] %(message)s",
    handlers=[
        logging.FileHandler("/var/log/channel_rebalancer.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("rebalancer")


def lncli(*args):
    cmd = ["lncli", "--tlscertpath=" + LND_CERT,
           "--macaroonpath=" + LND_MACAROON] + list(args)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=30)
    return p.returncode, out.strip(), err.strip()


def load_ledger():
    try:
        if REBALANCE_LEDGER.exists():
            return json.loads(REBALANCE_LEDGER.read_text())
    except:
        pass
    return {"rebalances": [], "total_sats_rebalanced": 0, "count": 0}


def save_ledger(d):
    REBALANCE_LEDGER.write_text(json.dumps(d, indent=2))


def get_amda_balance():
    """Obtiene balance de AMDA en el canal compartido."""
    rc, out, _ = lncli("listchannels")
    if rc != 0:
        return 0, 0
    try:
        data = json.loads(out)
        for c in data.get("channels", []):
            rpk = c.get("remote_pubkey", "")
            if rpk.startswith(AMDA_PUBKEY[:30]):
                remote = int(c.get("remote_balance", 0))
                local = int(c.get("local_balance", 0))
                return remote, local
    except:
        pass
    return 0, 0


def keysend(pubkey, sats):
    """Envía sats vía keysend a un nodo."""
    log.info("Keysend %d sats -> %s..." % (sats, pubkey[:16]))
    rc, out, err = lncli("sendpayment", "--dest", pubkey,
                         "--amt", str(sats),
                         "--keysend", "--force")
    if rc == 0:
        try:
            result = json.loads(out)
            ph = result.get("payment_hash", out[:20])
            log.info("Keysend EXITOSO! hash: %s..." % str(ph)[:20])
            return True, str(ph)[:32]
        except:
            log.info("Keysend EXITOSO!")
            return True, out[:32]
    else:
        log.warning("Keysend fallo: %s" % err[:100])
        return False, err[:100]


def check_and_rebalance():
    """Verifica balance de AMDA y rebalancea si es necesario."""
    amda_balance, catedral_balance = get_amda_balance()
    log.info("Canal AMDA: %d sats | Catedral: %d sats" %
             (amda_balance, catedral_balance))

    if amda_balance >= LOW_WATERMARK:
        return {"rebalanced": False, "reason": "above_watermark",
                "amda": amda_balance}

    if catedral_balance < REBALANCE_AMOUNT + 100:
        log.warning("Catedral sin suficiente liquidez: %d sats" % catedral_balance)
        return {"rebalanced": False, "reason": "catedral_low",
                "amda": amda_balance, "catedral": catedral_balance}

    rebal_amount = min(REBALANCE_AMOUNT, catedral_balance - 200)
    if rebal_amount < 1000:
        log.warning("Monto de rebalanceo muy bajo: %d" % rebal_amount)
        return {"rebalanced": False, "reason": "low_amount", "amount": rebal_amount}

    success, result = keysend(AMDA_PUBKEY, rebal_amount)
    if success:
        ledger = load_ledger()
        record = {
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "amount": rebal_amount,
            "from": "Catedral",
            "to": "AMDA",
            "amda_before": amda_balance,
            "catedral_before": catedral_balance,
            "result": result,
            "sello": ".|.𓂀Oo.o . TUYOYOTU . HECHO ESTA",
        }
        ledger["rebalances"].append(record)
        ledger["total_sats_rebalanced"] += rebal_amount
        ledger["count"] += 1
        ledger["last_rebalance"] = record["timestamp"]
        save_ledger(ledger)
        log.info("REBALANCE EXITOSO: %d sats -> AMDA" % rebal_amount)
        return {"rebalanced": True, "amount": rebal_amount}

    return {"rebalanced": False, "reason": "keysend_failed", "error": result}


def daemon_loop():
    log.info("=" * 60)
    log.info("🌀 CHANNEL REBALANCER — ACTIVO")
    log.info("   AMDA pubkey: %s..." % AMDA_PUBKEY[:16])
    log.info("   Watermark: %d sats" % LOW_WATERMARK)
    log.info("   Rebalance: %d sats" % REBALANCE_AMOUNT)
    log.info("   Ciclo: cada %ds" % CHECK_INTERVAL)
    log.info("=" * 60)

    while True:
        try:
            r = check_and_rebalance()
            if r.get("rebalanced"):
                log.info("Rebalance realizado: %d sats" % r["amount"])
        except Exception as e:
            log.error("Error: %s" % str(e))
        time.sleep(CHECK_INTERVAL)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "daemon"
    if mode == "daemon":
        daemon_loop()
    elif mode == "once":
        r = check_and_rebalance()
        print(json.dumps(r, indent=2))
    elif mode == "status":
        ledger = load_ledger()
        amda, cat = get_amda_balance()
        print("=== REBALANCE STATUS ===")
        print("AMDA canal:      %d sats" % amda)
        print("Catedral canal:  %d sats" % cat)
        print("Watermark:       %d sats" % LOW_WATERMARK)
        print("Rebalances:      %d" % ledger.get("count", 0))
        print("Total rebalance: %d sats" % ledger.get("total_sats_rebalanced", 0))
        print("Ultimo:          %s" % ledger.get("last_rebalance", "Nunca"))
    else:
        print("Uso: %s [daemon|once|status]" % sys.argv[0])
