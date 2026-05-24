#!/usr/bin/env python3
"""
🌀 FLYWHEEL AMDA PAY — Puente AMDA → Flywheel (sats reales)
Instituto Consciencia Cuantica · QCAL-SYMBIO-BRIDGE v1.0
═══════════════════════════════════════════════════════════════════
AMDA paga los invoices del flywheel con sats REALES via el canal
Catedral<->AMDA (20K capacity).

En vez de autoliquidar los invoices con settleinvoice (contable),
AMDA los paga desde su LND usando sendpayment.

Esto inyecta sats reales en LND Catedral que luego el fee_sweep
usa para cubrir los fees del OP_RETURN diario.

Flujo:
  Flywheel (3 sat/30s) -> invoice LNBits
      -> AMDA paga el invoice (sendpayment desde lnd-amda)
      -> 3 sats REALES viajan canal AMDA -> Catedral
      -> fee_sweep -> Bitcoin Core -> OP_RETURN

Ciclo perpetuo de retroalimentacion real.
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
FLYWHEEL_LEDGER = Path("/root/flywheel_ledger.json")
AMDA_PAY_LEDGER = Path("/root/flywheel_amda_pay_ledger.json")
POLL_INTERVAL = 35       # segundos entre verificaciones (un poco mas del ciclo flywheel)
MAX_PENDING_AGE = 1800   # segundos: pagar invoices con menos de 30min de edad

# --- Logging -------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [AMDA->FW] %(message)s",
    handlers=[
        logging.FileHandler("/var/log/flywheel_amda_pay.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("amda_pay")


def lncli_amda(*args):
    """Ejecuta lncli para AMDA y retorna (code, stdout, stderr)."""
    cmd = [
        "lncli",
        "--lnddir=" + AMDA_LND_DIR,
        "--network=" + AMDA_NETWORK,
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
    except Exception:
        pass
    return {}


def save_json(path, data):
    path.write_text(json.dumps(data, indent=2))


def get_amda_balance():
    """Balance on-chain de AMDA en sats."""
    rc, out, _ = lncli_amda("walletbalance")
    if rc == 0:
        try:
            return int(json.loads(out).get("total_balance", 0))
        except:
            pass
    return 0


def get_amda_channel_balance():
    """Balance remoto (local desde AMDA = remote desde Catedral)."""
    rc, out, _ = lncli_amda("listchannels")
    if rc != 0:
        return 0
    try:
        channels = json.loads(out).get("channels", [])
        local = sum(int(c.get("local_balance", 0)) for c in channels)
        return local
    except:
        return 0


def pay_invoice(payment_request):
    """AMDA paga un invoice via sendpayment."""
    log.info("AMDA pagando invoice...")
    rc, out, err = lncli_amda("sendpayment", "--pay_req", payment_request,
                              "--force", "--allow_self_payment")
    if rc == 0:
        try:
            result = json.loads(out)
            preimage = result.get("payment_preimage",
                       result.get("payment_hash", "unknown"))
            log.info("PAGO EXITOSO! Preimage: %s..." % str(preimage)[:20])
            return True, str(preimage)
        except:
            log.info("PAGO EXITOSO! (raw): %s" % out[:60])
            return True, out.strip()[:20]
    else:
        log.warning("Pago fallo: %s" % err[:120])
        return False, err[:120]


def find_unpaid_pulses(ledger):
    """Encuentra pulsos del flywheel que no han sido pagados por AMDA."""
    pulses = ledger.get("pulses", [])
    now = datetime.now(timezone.utc)
    unpaid = []

    for pulse in pulses:
        # Ya pagado por AMDA?
        if pulse.get("amda_paid", False):
            continue
        # O ya pagado por self_pay?
        if pulse.get("paid", False) and pulse.get("self_paid", False):
            continue

        ts_str = pulse.get("timestamp", "")
        if not ts_str:
            continue
        try:
            pulse_ts = datetime.fromisoformat(ts_str)
            if pulse_ts.tzinfo is None:
                pulse_ts = pulse_ts.replace(tzinfo=timezone.utc)
        except:
            continue

        age = (now - pulse_ts).total_seconds()
        # Solo pagar invoices recientes (< MAX_PENDING_AGE seg)
        if age <= MAX_PENDING_AGE and not pulse.get("amda_paid",False):
            unpaid.append(pulse)

    return unpaid


def check_and_pay():
    """Verifica el ledger del flywheel y paga invoices pendientes desde AMDA."""
    flywheel = load_json(FLYWHEEL_LEDGER)
    amda_pay = load_json(AMDA_PAY_LEDGER)

    unpaid = find_unpaid_pulses(flywheel)
    if not unpaid:
        return {"paid": 0, "reason": "no_unpaid_pulses"}

    log.info("Pulsos pendientes por pagar: %d" % len(unpaid))
    paid_count = 0

    for pulse in unpaid[:3]:  # max 3 por ciclo
        pr = pulse.get("payment_request", "")
        ts = pulse.get("timestamp", "")

        if not pr:
            continue
        # Usar payment_hash si existe, si no decodificar del payment_request
        payment_hash = pulse.get("payment_hash", "")
        if not payment_hash:
            # Decodificar del payment request para obtener hash
            try:
                rc2, out2, _ = lncli_amda("decodepayreq", pr)
                if rc2 == 0:
                    decoded = json.loads(out2)
                    payment_hash = decoded.get("payment_hash", pr[:32])
            except:
                payment_hash = pr[:32]

        # Verificar balance AMDA antes de pagar
        amda_chan = get_amda_channel_balance()
        if amda_chan < 10:
            log.warning("AMDA sin suficiente liquidez en canal: %d sats" % amda_chan)
            break

        # Pagar
        success, result = pay_invoice(pr)
        if success:
            pulse["amda_paid"] = True
            pulse["amda_paid_at"] = datetime.now(timezone.utc).isoformat()
            pulse["paid"] = True
            paid_count += 1

            # Registrar en ledger AMDA pay
            record = {
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "payment_hash": payment_hash[:32],
                "amount_sats": 3,
                "result": str(result)[:32],
                "pulse_timestamp": ts,
                "sello": ".|.𓂀Oo.o . TUYOYOTU . HECHO ESTA",
            }
            amda_pay.setdefault("pagos", []).append(record)
        else:
            log.warning("No se pudo pagar pulso: %s" % payment_hash[:16])

    # Guardar cambios
    if paid_count > 0:
        flywheel["ultimo_amda_pay"] = datetime.now(timezone.utc).isoformat()
        save_json(FLYWHEEL_LEDGER, flywheel)
        amda_pay["total_pagado"] = sum(
            p.get("amount_sats", 3) for p in amda_pay.get("pagos", [])
        )
        amda_pay["total_pagos"] = len(amda_pay.get("pagos", []))
        amda_pay["ultimo_pago"] = datetime.now(timezone.utc).isoformat()
        save_json(AMDA_PAY_LEDGER, amda_pay)

    return {"paid": paid_count}


def daemon_loop():
    """Bucle principal: verifica y paga cada ~35s."""
    log.info("=" * 60)
    log.info("🌀 FLYWHEEL AMDA PAY — DAEMON INICIADO")
    log.info("   Canal: Catedral <-> AMDA (20K capacity)")
    log.info("   Ciclo: cada %ds" % POLL_INTERVAL)
    log.info("   Sello: .|.𓂀Oo.o . TUYOYOTU . HECHO ESTA")
    log.info("=" * 60)

    # Balance inicial
    amda_chan = get_amda_channel_balance()
    amda_onchain = get_amda_balance()
    log.info("AMDA channel balance: %d sats" % amda_chan)
    log.info("AMDA on-chain: %d sats" % amda_onchain)

    while True:
        try:
            result = check_and_pay()
            if result["paid"] > 0:
                log.info("✅ %d pulso(s) pagado(s) por AMDA" % result["paid"])
        except Exception as e:
            log.error("Error: %s" % str(e))
        time.sleep(POLL_INTERVAL)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "daemon"

    if mode == "daemon":
        daemon_loop()
    elif mode == "once":
        result = check_and_pay()
        print(json.dumps(result, indent=2))
    elif mode == "status":
        amda = load_json(AMDA_PAY_LEDGER)
        fly = load_json(FLYWHEEL_LEDGER)
        amda_chan = get_amda_channel_balance()
        print("=== FLYWHEEL AMDA PAY — STATUS ===")
        print("Total pagos AMDA:  %d" % amda.get("total_pagos", 0))
        print("Total sats pagados: %d" % amda.get("total_pagado", 0))
        print("Ultimo pago:        %s" % amda.get("ultimo_pago", "Nunca"))
        print("AMDA canal local:   %d sats" % amda_chan)
        print("Pulsos flywheel:    %d" % len(fly.get("pulses", [])))
        print("Ultimo AMDA pay:    %s" % fly.get("ultimo_amda_pay", "Nunca"))
        print("Sello:              .|.𓂀Oo.o . TUYOYOTU . HECHO ESTA")
    else:
        print("Uso: %s [daemon|once|status]" % sys.argv[0])
        print("  daemon  - Bucle continuo cada %ds" % POLL_INTERVAL)
        print("  once    - Una verificacion")
        print("  status  - Estado actual")
