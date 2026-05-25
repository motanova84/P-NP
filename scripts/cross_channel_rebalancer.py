#!/usr/bin/env python3
"""
🌀 CROSS-CHANNEL REBALANCER — Mueve sats del canal AMDA al canal externo
Instituto Consciencia Cuantica · QCAL-SYMBIO-BRIDGE v1.0
═══════════════════════════════════════════════════════════════════
Cuando Catedral tiene suficientes sats en el canal AMDA, los mueve
al canal externo via pago circular para mantener liquidez en ambos.

Flujo:
  AMDA keysend 333 -> Catedral (canal AMDA)
    -> cuando canal AMDA > 10K, mover 5K al canal externo
    -> canal externo lleno -> pago Lightning a Wallet of Satoshi

No afecta a AMDA. Solo usa sats sobrantes de Catedral.
═══════════════════════════════════════════════════════════════════
"""

import json, logging, subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path

# Constantes
LND_CERT = "/root/.lnd/tls.cert"
LND_MAC = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
AMDA_PUBKEY = "037e6a4145516fdd7b455c1d63cb07183f082e9ee122cfeff8a5c6cdb5acb36ba0"
AMDA_CHAN_THRESHOLD = 10000  # Cuando canal AMDA de Catedral > 10K, mover
MOVE_AMOUNT = 5000           # Sats a mover del canal AMDA al externo
EXTERNAL_CHAN_THRESHOLD = 2000  # Si canal externo < 2K, recargar
CHECK_INTERVAL = 60
LEDGER = Path("/root/cross_channel_rebalance_ledger.json")

logging.basicConfig(level=logging.INFO, format="%(asctime)s [XR] %(message)s",
    handlers=[logging.FileHandler("/var/log/cross_channel_rebalance.log"), logging.StreamHandler()])
log = logging.getLogger("cross_rebal")

def lncli(*a):
    cmd = ["lncli", "--tlscertpath=" + LND_CERT, "--macaroonpath=" + LND_MAC] + list(a)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=30)
    return p.returncode, out.strip(), err.strip()

def load_json(p):
    try:
        if p.exists(): return json.loads(p.read_text())
    except: pass
    return {"rebalances": [], "total_sats_moved": 0, "count": 0}

def save_json(p, d):
    p.write_text(json.dumps(d, indent=2))

def get_channel_balances():
    """Retorna balances de AMDA y externo."""
    rc, out, _ = lncli("listchannels")
    if rc != 0: return 0, 0, 0, 0
    try:
        data = json.loads(out)
        amda_local = 0; amda_remote = 0
        ext_local = 0; ext_remote = 0
        for c in data.get("channels", []):
            rpk = c.get("remote_pubkey", "")
            if AMDA_PUBKEY.startswith(rpk[:len(AMDA_PUBKEY)]):
                amda_local = int(c.get("local_balance", 0))
                amda_remote = int(c.get("remote_balance", 0))
            elif not rpk.startswith(AMDA_PUBKEY[:20]):
                ext_local = int(c.get("local_balance", 0))
                ext_remote = int(c.get("remote_balance", 0))
        return amda_local, amda_remote, ext_local, ext_remote
    except: return 0, 0, 0, 0

def circular_rebalance(target_pubkey, amount):
    """Rebalancea moviendo sats via pago circular."""
    log.info("Rebalanceando %d sats -> canal externo..." % amount)
    # Keysend a traves del peer externo para mover sats de canal
    rc, out, err = lncli("sendpayment", "--dest", target_pubkey,
                         "--amt", str(amount), "--keysend", "--force")
    if rc == 0:
        log.info("Rebalance exitoso!")
        return True
    log.warning("Rebalance fallo: %s" % err[:80])
    return False

def check_and_rebalance():
    amda_loc, amda_rem, ext_loc, ext_rem = get_channel_balances()
    log.info("Canales - AMDA: %d/%d | Externo: %d/%d" %
             (amda_loc, amda_rem, ext_loc, ext_rem))

    if ext_loc == 0 and ext_rem == 0:
        log.info("Canal externo aun no abierto.")
        return {"rebalanced": False, "reason": "no_external_channel"}

    if amda_loc < AMDA_CHAN_THRESHOLD:
        log.info("Canal AMDA bajo (%d), sin excedentes para mover." % amda_loc)
        return {"rebalanced": False, "reason": "amda_low"}

    if ext_loc > EXTERNAL_CHAN_THRESHOLD:
        log.info("Canal externo OK (%d), no necesita recarga." % ext_loc)
        return {"rebalanced": False, "reason": "external_ok"}

    move = min(MOVE_AMOUNT, amda_loc - 3000)  # dejar 3K a AMDA
    if move < 1000:
        log.info("Poco margen para mover: %d sats" % move)
        return {"rebalanced": False, "reason": "low_margin"}

    # Por ahora: keysend a AMDA como placeholder
    # (cuando el canal externo exista, esto se cambia)
    success = circular_rebalance(AMDA_PUBKEY, move)
    if not success:
        return {"rebalanced": False, "reason": "rebalance_failed"}

    ledger = load_json(LEDGER)
    record = {"timestamp": datetime.now(timezone.utc).isoformat(),
              "amount": move, "amda_before": amda_loc, "ext_before": ext_loc,
              "sello": ".|.𓂀Oo.o . TUYOYOTU . HECHO ESTA"}
    ledger["rebalances"].append(record)
    ledger["total_sats_moved"] += move
    ledger["count"] += 1
    ledger["last_rebalance"] = record["timestamp"]
    save_json(LEDGER, ledger)
    log.info("Cross-rebalance: %d sats movidos" % move)
    return {"rebalanced": True, "amount": move}

def daemon():
    log.info("="*60)
    log.info("🌀 CROSS-CHANNEL REBALANCER")
    log.info("   Esperando canal externo...")
    log.info("="*60)
    while True:
        try:
            r = check_and_rebalance()
            if r.get("rebalanced"):
                log.info("%d sats movidos" % r["amount"])
        except Exception as e:
            log.error("Error: %s" % str(e))
        time.sleep(CHECK_INTERVAL)

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "daemon"
    if mode == "daemon":
        daemon()
    elif mode == "once":
        r = check_and_rebalance()
        print(json.dumps(r, indent=2))
    elif mode == "status":
        amda_loc, amda_rem, ext_loc, ext_rem = get_channel_balances()
        ledger = load_json(LEDGER)
        print("=== CROSS-CHANNEL REBALANCE ===")
        print("Canal AMDA:     %d/%d sats" % (amda_loc, amda_rem))
        print("Canal externo:  %d/%d sats" % (ext_loc, ext_rem))
        print("Rebalances:     %d" % ledger.get("count", 0))
        print("Sats movidos:   %d" % ledger.get("total_sats_moved", 0))
        print("Umbral AMDA:    %d sats" % AMDA_CHAN_THRESHOLD)
        print("Umbral externo: %d sats" % EXTERNAL_CHAN_THRESHOLD)
