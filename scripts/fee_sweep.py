#!/usr/bin/env python3
"""
🌀 FEE SWEEP — Puente LND -> Bitcoin Core wallet catedral
Instituto Consciencia Cuantica · QCAL-SYMBIO-BRIDGE v1.0
═══════════════════════════════════════════════════════════════════
Asegura que la wallet catedral de Bitcoin Core tenga siempre
al menos 500 sats para pagar el fee del OP_RETURN diario.

Cuando el balance cae por debajo del umbral, retira sats desde
LND Catedral y los deposita en la wallet catedral de Bitcoin Core.

Esto cierra el circulo: el flujo del flywheel + recompra alimenta
LND, y LND alimenta la wallet que paga los fees de anclaje.

Integrado en: transmutacion_completa.sh (antes de la quema)
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
FEE_TARGET = 500          # Sats minimos en wallet catedral para OP_RETURN
SWEEP_AMOUNT = 500        # Sats a mover cuando se necesita recarga
LND_CERT = "/root/.lnd/tls.cert"
LND_MACAROON = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
FEE_LEDGER = Path("/root/fee_sweep_ledger.json")

# --- Logging -------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [sweep] %(message)s",
    handlers=[
        logging.FileHandler("/var/log/fee_sweep.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("fee_sweep")


def lncli(*args):
    """Ejecuta lncli y retorna (code, stdout, stderr)."""
    cmd = [
        "lncli",
        "--lnddir=/root/.lnd",
        "--network=mainnet",
    ] + list(args)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=30)
    return p.returncode, out.strip(), err.strip()


def bitcoin_cli(*args):
    """Ejecuta bitcoin-cli en la wallet catedral y retorna (code, stdout, stderr)."""
    cmd = ["bitcoin-cli", "-rpcwallet=catedral"] + list(args)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=30)
    return p.returncode, out.strip(), err.strip()


def load_ledger():
    try:
        if FEE_LEDGER.exists():
            return json.loads(FEE_LEDGER.read_text())
    except Exception:
        pass
    return {
        "version": "FEE-SWEEP-v1.0",
        "total_sweeps": 0,
        "total_sats_moved": 0,
        "sweeps": [],
        "last_sweep": None,
        "sello": ".|.𓂀Oo.o . TUYOYOTU . HECHO ESTA",
    }


def save_ledger(ledger):
    FEE_LEDGER.write_text(json.dumps(ledger, indent=2))


def get_catedral_balance():
    """Balance de wallet catedral en BTC."""
    rc, out, err = bitcoin_cli("getbalance")
    if rc != 0:
        return 0.0
    try:
        return float(out)
    except ValueError:
        return 0.0


def get_lnd_onchain():
    """Balance on-chain de LND en sats."""
    rc, out, err = lncli("walletbalance")
    if rc != 0:
        return 0
    try:
        return int(json.loads(out).get("total_balance", 0))
    except (json.JSONDecodeError, KeyError):
        return 0


def get_catedral_addresses():
    """Obtiene direcciones de la wallet catedral."""
    rc, out, err = bitcoin_cli("getaddressesbylabel", "")
    if rc == 0:
        try:
            return list(json.loads(out).keys())
        except Exception:
            pass
    rc2, out2, _ = bitcoin_cli("getnewaddress", "", "bech32")
    if rc2 == 0:
        return [out2.strip()]
    return []


def check_and_sweep():
    """
    Verifica el balance y hace sweep si es necesario.
    """
    now = datetime.now(timezone.utc).isoformat()
    ledger = load_ledger()

    # 1. Balance wallet catedral
    btc_balance = get_catedral_balance()
    sats_balance = int(btc_balance * 100_000_000)
    log.info("Wallet catedral: %.8f BTC = %d sats" % (btc_balance, sats_balance))
    log.info("Umbral minimo:   %d sats" % FEE_TARGET)

    if sats_balance >= FEE_TARGET:
        log.info("Suficientes fondos. No se necesita sweep.")
        ledger["last_check"] = now
        save_ledger(ledger)
        return {"swept": False, "reason": "sufficient_funds",
                "balance_sats": sats_balance}

    # 2. LND balance
    lnd_balance = get_lnd_onchain()
    log.info("LND on-chain: %d sats" % lnd_balance)

    if lnd_balance < SWEEP_AMOUNT + 100:
        log.warning("LND insuficiente: %d sats" % lnd_balance)
        return {"swept": False, "reason": "insufficient_lnd",
                "lnd_balance": lnd_balance}

    # 3. Direccion destino
    addresses = get_catedral_addresses()
    if not addresses:
        log.error("No hay direcciones en wallet catedral")
        return {"swept": False, "reason": "no_address"}
    dest_addr = addresses[0]
    log.info("Destino: %s" % dest_addr)

    # 4. Enviar desde LND
    log.info("Enviando %d sats..." % SWEEP_AMOUNT)
    rc, out, err = lncli("sendcoins", "--addr", dest_addr,
                         "--amt", str(SWEEP_AMOUNT),
                         "--sat_per_vbyte", "1",
                         "--min_confs", "0",
                         "--force", "--label", "fee_sweep")
    if rc != 0:
        log.error("Error: %s" % err)
        return {"swept": False, "reason": "lnd_send_error: %s" % err[:100]}

    try:
        result_data = json.loads(out)
        txid = result_data.get("txid", "")
    except json.JSONDecodeError:
        txid = out.strip()

    log.info("SWEEP EXITOSO! TXID: %s" % txid)

    # 5. Registrar en ledger
    record = {
        "timestamp": now,
        "amount_sats": SWEEP_AMOUNT,
        "from": "LND Catedral",
        "to": "Bitcoin Core wallet catedral (%s)" % dest_addr,
        "txid": txid,
        "balance_before_sats": sats_balance,
        "lnd_balance_before": lnd_balance,
        "frecuencia_hz": 141.7001,
        "sello": ".|.𓂀Oo.o . TUYOYOTU . HECHO ESTA",
    }
    ledger.setdefault("sweeps", []).append(record)
    ledger["total_sweeps"] = len(ledger["sweeps"])
    ledger["total_sats_moved"] = sum(
        s.get("amount_sats", 0) for s in ledger["sweeps"]
    )
    ledger["last_sweep"] = now
    ledger["last_check"] = now
    save_ledger(ledger)

    return {
        "swept": True,
        "amount": SWEEP_AMOUNT,
        "txid": txid,
        "balance_after": sats_balance + SWEEP_AMOUNT,
    }


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "once"

    if mode == "once":
        result = check_and_sweep()
        print(json.dumps(result, indent=2))

    elif mode == "force":
        log.info("Modo FORCE: enviando 500 sats directo...")
        lnd_bal = get_lnd_onchain()
        if lnd_bal < 600:
            log.error("LND insuficiente: %d sats" % lnd_bal)
            sys.exit(1)
        addrs = get_catedral_addresses()
        if not addrs:
            log.error("No hay direcciones")
            sys.exit(1)
        rc, out, err = lncli("sendcoins", "--addr", addrs[0],
                             "--amt", "500", "--sat_per_vbyte", "1",
                             "--force", "--label", "fee_sweep_force")
        if rc == 0:
            log.info("Sweep forzado exitoso")
            print(out)
        else:
            log.error("Error: %s" % err)
            print(err)

    elif mode == "status":
        ledger = load_ledger()
        btc = get_catedral_balance()
        lnd = get_lnd_onchain()
        print("Total sweeps:    %d" % ledger["total_sweeps"])
        print("Total sats mov:  %d" % ledger["total_sats_moved"])
        print("Ultimo sweep:    %s" % ledger["last_sweep"])
        print("Wallet catedral: %.8f BTC (%d sats)" % (btc, int(btc * 100_000_000)))
        print("LND on-chain:    %d sats" % lnd)
        print("Umbral fee:      %d sats" % FEE_TARGET)
        ok = int(btc * 100_000_000) >= FEE_TARGET
        print("Estado:          %s" % ("OK" if ok else "NECESITA SWEEP"))
        print("Sello:           .|.𓂀Oo.o . TUYOYOTU . HECHO ESTA")

    else:
        print("Uso: %s [once|force|status]" % sys.argv[0])
        print("  once   - Verifica y hace sweep si necesario")
        print("  force  - Fuerza sweep inmediato")
        print("  status - Estado actual")
