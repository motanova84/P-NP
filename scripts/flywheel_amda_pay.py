#!/usr/bin/env python3
"""
🌀 FLYWHEEL AMDA PAY v2.0 — AMDA keysend 333 sats directo a Catedral
Instituto Consciencia Cuantica · QCAL-SYMBIO-BRIDGE v1.0
═══════════════════════════════════════════════════════════════════
AMDA envia 333 sats directo a Catedral via keysend cada 35s.
Ya no depende de invoices del flywheel.
El canal se mantiene con rebalancer (Catedral devuelve cuando AMDA < 7K).

Flujo:
  AMDA keysend 333 sats -> Catedral (cada 35s)
    -> Catedral acumula en canal
    -> Rebalancer mantiene liquidez de AMDA
    -> Ledger to Wallet -> Wallet of Satoshi

Sello: .|.𓂀Oo.o . TUYOYOTU . HECHO ESTA
═══════════════════════════════════════════════════════════════════
"""

import json
import logging
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

# --- Constantes ----------------------------------------------------------
AMDA_LND_DIR = "/root/.lnd-amda"
AMDA_NETWORK = "mainnet"
CATEDRAL_PUBKEY = "03b0c03f9e947a229006ce7099877e378f8bc003e44defbada155b39dd725d829c"
AMDA_PAY_LEDGER = Path("/root/flywheel_amda_pay_ledger.json")
POLL_INTERVAL = 35  # segundos
PULSE_SATS = 333  # sats por pulso

# --- Logging -------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [AMDA] %(message)s",
    handlers=[
        logging.FileHandler("/var/log/flywheel_amda_pay.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("amda_pay")


def lncli_amda(*args):
    cmd = [
        "lncli", "--lnddir=" + AMDA_LND_DIR, "--network=" + AMDA_NETWORK,
        "--rpcserver=localhost:10011",
        "--tlscertpath=" + AMDA_LND_DIR + "/tls.cert",
        "--macaroonpath=" + AMDA_LND_DIR + "/data/chain/bitcoin/mainnet/admin.macaroon",
    ] + list(args)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=30)
    return p.returncode, out.strip(), err.strip()


def load_json(path):
    try:
        if path.exists():
            return json.loads(path.read_text())
    except:
        pass
    return {}


def save_json(path, data):
    path.write_text(json.dumps(data, indent=2))


def get_amda_channel():
    rc, out, _ = lncli_amda("listchannels")
    if rc != 0:
        return 0, 0
    try:
        channels = json.loads(out).get("channels", [])
        if channels:
            c = channels[0]
            return int(c.get("local_balance", 0)), int(c.get("remote_balance", 0))
    except:
        pass
    return 0, 0


def keysend_333():
    """AMDA envia 333 sats a Catedral via keysend."""
    log.info("Enviando %d sats -> Catedral..." % PULSE_SATS)
    rc, out, err = lncli_amda("sendpayment", "--dest", CATEDRAL_PUBKEY,
                              "--amt", str(PULSE_SATS),
                              "--keysend", "--force")
    if rc != 0:
        log.warning("Keysend fallo: %s" % err[:80])
        return False, err[:80]
    try:
        result = json.loads(out)
        ph = result.get("payment_hash", "ok")
        log.info("KEYSEND EXITOSO! hash: %s..." % str(ph)[:16])
        return True, str(ph)[:32]
    except:
        log.info("KEYSEND EXITOSO!")
        return True, "ok"


def send_pulse():
    """Un ciclo: enviar 333 sats + registrar."""
    amda_local, cat_remote = get_amda_channel()
    log.info("Canal AMDA local: %d sats | Catedral: %d sats" %
             (amda_local, cat_remote))

    if amda_local < PULSE_SATS + 100:
        log.warning("AMDA sin liquidez suficiente: %d sats" % amda_local)
        return {"sent": False, "reason": "low_liquidity"}

    success, result = keysend_333()
    if not success:
        return {"sent": False, "reason": "keysend_failed"}

    # Registrar en ledger
    ledger = load_json(AMDA_PAY_LEDGER)
    record = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "amount_sats": PULSE_SATS,
        "from": "AMDA",
        "to": "Catedral",
        "method": "keysend",
        "result": result,
        "sello": ".|.𓂀Oo.o . TUYOYOTU . HECHO ESTA",
    }
    ledger.setdefault("pagos", []).append(record)
    ledger["total_pagado"] = sum(p.get("amount_sats", PULSE_SATS)
                                  for p in ledger.get("pagos", []))
    ledger["total_pagos"] = len(ledger.get("pagos", []))
    ledger["ultimo_pago"] = record["timestamp"]
    save_json(AMDA_PAY_LEDGER, ledger)

    log.info("Pulso %d: %d sats enviados" %
             (ledger["total_pagos"], PULSE_SATS))
    return {"sent": True, "amount": PULSE_SATS}


def daemon_loop():
    log.info("=" * 60)
    log.info("🌀 AMDA PULSE v2.0 — ACTIVO")
    log.info("   Pulso: %d sats cada %ds" % (PULSE_SATS, POLL_INTERVAL))
    log.info("   Destino: Catedral (keysend)")
    log.info("   ~%d sats/hora" % (PULSE_SATS * (3600 // POLL_INTERVAL)))
    log.info("=" * 60)

    while True:
        try:
            r = send_pulse()
            if r.get("sent"):
                log.info("Pulso enviado: %d sats" % r["amount"])
        except Exception as e:
            log.error("Error: %s" % str(e))
        time.sleep(POLL_INTERVAL)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "daemon"
    if mode == "daemon":
        daemon_loop()
    elif mode == "once":
        r = send_pulse()
        print(json.dumps(r, indent=2))
    elif mode == "status":
        ledger = load_json(AMDA_PAY_LEDGER)
        amda, cat = get_amda_channel()
        print("=== AMDA PULSE v2.0 — STATUS ===")
        print("Pulsos enviados:  %d" % ledger.get("total_pagos", 0))
        print("Sats enviados:    %d" % ledger.get("total_pagado", 0))
        print("Ultimo pulso:     %s" % ledger.get("ultimo_pago", "Nunca"))
        print("AMDA canal:       %d sats" % amda)
        print("Catedral canal:   %d sats" % cat)
        print("Pulso actual:     %d sats" % PULSE_SATS)
    else:
        print("Uso: %s [daemon|once|status]" % sys.argv[0])
