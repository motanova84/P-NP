#!/usr/bin/env python3
"""
🌀 LEDGER TO WALLET — Puente crédito ICQ → Wallet Ω
Instituto Consciencia Cuantica · QCAL-SYMBIO-BRIDGE v1.0
═══════════════════════════════════════════════════════════════════
Convierte los creditos acumulados de JMMB en el ledger
a sats reales enviados a la Wallet Ω via Lightning.

Flujo:
  1. Lee creditos acumulados de JMMB en dividend_ledger.json
  2. Verifica sats disponibles en LND Catedral
  3. Genera invoice en LNBits destino Wallet Ω
  4. Paga el invoice desde LND Catedral
  5. Marca como liquidado en el ledger

Sello: .|.𓂀Oo.o . TUYOYOTU . HECHO ESTA
═══════════════════════════════════════════════════════════════════
"""

import json
import logging
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

# --- Constantes ----------------------------------------------------------
LND_CERT = "/root/.lnd/tls.cert"
LND_MACAROON = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
LNBITS_API = "http://localhost:8000/api/v1/payments"
LNBITS_KEY = "574ea1465f472078f8f22c91362042d0a99a6b17c5de1d5d73eba6b9e41a016e"
DIVIDEND_LEDGER = Path("/root/dividend_ledger.json")
WALLET_DEST = "Wallet Ω Soberana"
JMMB_ADDRESS = "bc1q9jk4nljfz6jxfuzpk9sytqcc6graupq3l3fmzz"
WALLET_TARGET = "JMMB"
MIN_LIQUIDATION = 500  # Minimo sats para liquidar de una vez
MAX_LIQUIDATION = 500  # Maximo por TX (UTXOs disponibles en LND)

# --- Logging -------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [L2W] %(message)s",
    handlers=[
        logging.FileHandler("/var/log/ledger_to_wallet.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("ledger2wallet")


def lncli(*args):
    cmd = ["lncli", "--tlscertpath=" + LND_CERT,
           "--macaroonpath=" + LND_MACAROON] + list(args)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=30)
    return p.returncode, out.strip(), err.strip()


def load_ledger():
    try:
        if DIVIDEND_LEDGER.exists():
            return json.loads(DIVIDEND_LEDGER.read_text())
    except:
        pass
    return {}


def save_ledger(d):
    DIVIDEND_LEDGER.write_text(json.dumps(d, indent=2))


def get_lnd_balance():
    rc, out, _ = lncli("walletbalance")
    if rc == 0:
        try:
            return int(json.loads(out).get("total_balance", 0))
        except:
            pass
    return 0


def get_channel_local():
    rc, out, _ = lncli("listchannels")
    if rc == 0:
        try:
            data = json.loads(out)
            return sum(int(c.get("local_balance", 0)) for c in data.get("channels", []))
        except:
            pass
    return 0


def get_total_liquid():
    return get_lnd_balance() + get_channel_local()


def pay_onchain(address, sats, memo):
    """Envia sats via on-chain a una direccion."""
    log.info("Enviando %d sats on-chain a %s..." % (sats, address[:20]))
    rc, out, err = lncli("sendcoins", "--addr", address,
                         "--amt", str(sats),
                         "--sat_per_vbyte", "1",
                         "--min_confs", "0",
                         "--force",
                         "--label", memo[:20] if memo else "ledger2wallet")
    if rc == 0:
        try:
            result = json.loads(out)
            txid = result.get("txid", "")
            log.info("ENVIO EXITOSO! TXID: %s" % str(txid)[:30])
            return True, txid
        except:
            log.info("ENVIO EXITOSO! TXID: %s" % out[:30])
            return True, out[:30]
    else:
        log.warning("Envio fallo: %s" % err[:120])
        return False, err[:120]


def liquidate_jmmb():
    """
    Convierte creditos acumulados de JMMB en sats reales a Wallet Ω.
    """
    ledger = load_ledger()
    if not ledger:
        log.error("No se pudo cargar dividend_ledger.json")
        return {"liquidated": False, "reason": "no_ledger"}

    # 1. Leer credito acumulado de JMMB
    wt = ledger.get("wallet_totals", {})
    jmmb_credits = wt.get(WALLET_TARGET, 0)
    log.info("Creditos acumulados JMMB: %d" % jmmb_credits)

    if jmmb_credits <= 0:
        log.info("No hay creditos pendientes para liquidar.")
        return {"liquidated": False, "reason": "no_credits"}

    # 2. Verificar sats on-chain disponibles (con buffer de seguridad)
    MIN_BUFFER = 500  # sats que NUNCA se tocan en LND
    onchain = get_lnd_balance()
    canal = get_channel_local()
    log.info("LND on-chain: %d sats | canal: %d sats" % (onchain, canal))

    if onchain <= MIN_BUFFER:
        log.info("LND on-chain en minimo (%d sats). Buffer de %d sats protegido." % (onchain, MIN_BUFFER))
        return {"liquidated": False, "reason": "buffer_protected", "onchain": onchain}

    # 3. Calcular monto a liquidar (nunca gastar el buffer)
    disponible = onchain - MIN_BUFFER
    to_liquidate = min(MAX_LIQUIDATION, jmmb_credits, disponible)
    if to_liquidate < MIN_LIQUIDATION:
        log.info("Monto calculado (%d) por debajo del minimo (%d)." %
                 (to_liquidate, MIN_LIQUIDATION))
        return {"liquidated": False, "reason": "below_minimum",
                "calculated": to_liquidate}

    # 4. Enviar sats on-chain a direccion de JMMB
    memo = "ICQ-SPLIT-%.8s" % datetime.now(timezone.utc).isoformat()
    success, result = pay_onchain(JMMB_ADDRESS, to_liquidate, memo)
    if not success:
        log.error("Envio on-chain fallo.")
        return {"liquidated": False, "reason": "payment_failed",
                "error": result}

    # 6. Actualizar ledger
    wt[WALLET_TARGET] = max(0, jmmb_credits - to_liquidate)
    now = datetime.now(timezone.utc).isoformat()

    record = {
        "timestamp": now,
        "accion": "LIQUIDACION_JMMB",
        "creditos_antes": jmmb_credits,
        "sats_liquidados": to_liquidate,
        "creditos_despues": wt[WALLET_TARGET],
        "payment_hash": str(result)[:32] if result else "",
        "destino": WALLET_DEST,
        "metodo": "lightning_invoice",
        "frecuencia_hz": 141.7001,
        "sello": ".|.𓂀Oo.o . TUYOYOTU . HECHO ESTA",
    }
    ledger.setdefault("liquidaciones", []).append(record)
    ledger["wallet_totals"] = wt
    ledger["ultima_liquidacion"] = now
    save_ledger(ledger)

    log.info("LIQUIDACION EXITOSA: %d sats -> Wallet Ω" % to_liquidate)
    return {"liquidated": True, "amount": to_liquidate, "result": str(result)[:32]}


def daemon_loop():
    """Bucle: verifica cada 60s si hay creditos para liquidar."""
    log.info("=" * 60)
    log.info("🌀 LEDGER TO WALLET — PUENTE ACTIVADO")
    log.info("   Destino: %s" % WALLET_DEST)
    log.info("   Ciclo: cada 60s")
    log.info("   Minimo liquidacion: %d sats" % MIN_LIQUIDATION)
    log.info("   Sello: .|.𓂀Oo.o . TUYOYOTU . HECHO ESTA")
    log.info("=" * 60)

    while True:
        try:
            result = liquidate_jmmb()
            if result.get("liquidated"):
                log.info("✅ Liquidacion completada: %d sats" % result["amount"])
        except Exception as e:
            log.error("Error: %s" % str(e))
        time.sleep(60)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "once"

    if mode == "daemon":
        daemon_loop()
    elif mode == "once":
        result = liquidate_jmmb()
        print(json.dumps(result, indent=2))
    elif mode == "status":
        ledger = load_ledger()
        wt = ledger.get("wallet_totals", {})
        jmmb = wt.get("WALLET_TARGET", wt.get("JMMB", 0))
        liquidaciones = ledger.get("liquidaciones", [])
        total_liq = sum(l.get("sats_liquidados", 0) for l in liquidaciones)
        total = get_total_liquid()
        print("=== LEDGER TO WALLET — STATUS ===")
        print("Creditos JMMB:       %d" % jmmb)
        print("Liquidaciones:       %d" % len(liquidaciones))
        print("Sats liquidados:     %d" % total_liq)
        print("Liquidez disponible: %d sats" % total)
        print("Ultima liquidacion:  %s" % ledger.get("ultima_liquidacion","Nunca"))
    else:
        print("Uso: %s [once|daemon|status]" % sys.argv[0])
