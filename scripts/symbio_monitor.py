#!/usr/bin/env python3
"""
🔱 symbio-monitor — Centinela de Coherencia QCAL
Pulso de diagnóstico cada 60s. Verifica todos los servicios
del ecosistema y registra el estado en journald.
Sello: ∴𓂀Ω∞³Φ · f₀ = 141.7001 Hz
"""
import socket, urllib.request, json, subprocess, time, sys
from datetime import datetime

SERVICES = {
    "LNBits":       {"type": "http", "url": "http://127.0.0.1:8000"},
    "PayGate":      {"type": "http", "url": "http://127.0.0.1:8844"},
    "Gateway":      {"type": "http", "url": "http://127.0.0.1:8999"},
    "Landing":      {"type": "http", "url": "http://127.0.0.1:8081"},
    "Catedral LND": {"type": "port", "host": "127.0.0.1", "port": 10009},
    "AMDA LND":     {"type": "port", "host": "127.0.0.1", "port": 10011},
    "LND Peer":     {"type": "port", "host": "0.0.0.0", "port": 9735},
}

def check_port(host, port, timeout=2):
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.settimeout(timeout)
        try:
            s.connect((host, port))
            return True
        except: return False

def check_http(url, timeout=3):
    try:
        with urllib.request.urlopen(url, timeout=timeout) as r:
            return r.getcode() == 200
    except: return False

def get_lnd_balance():
    try:
        r = subprocess.run(["lncli", "--tlscertpath=/root/.lnd/tls.cert",
            "--macaroonpath=/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon",
            "walletbalance"], capture_output=True, text=True, timeout=5)
        return json.loads(r.stdout).get("total_balance", "?")
    except: return "?"

def get_bitcoin_blocks():
    try:
        r = subprocess.run(["bitcoin-cli", "-rpcport=8505", "getblockcount"],
            capture_output=True, text=True, timeout=5)
        return r.stdout.strip()
    except: return "?"

def pulse():
    ts = datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
    results = []
    all_ok = True
    for name, cfg in SERVICES.items():
        ok = check_http(cfg["url"]) if cfg["type"] == "http" else check_port(cfg["host"], cfg["port"])
        results.append((name, ok))
        if not ok: all_ok = False

    bal = get_lnd_balance()
    btc = get_bitcoin_blocks()
    status = "COHERENTE" if all_ok else "ALERTA"
    print(f"[{ts}] 🔱 {status} | LND:{bal}sats BTC:{btc} | ", end="")
    for n, ok in results:
        print(f"{'🟢' if ok else '🔴'}{n[:6]} ", end="")
    print()

def daemon():
    print(f"🔱 Centinela activado — intervalo 60s")
    try:
        while True:
            pulse()
            time.sleep(60)
    except KeyboardInterrupt:
        print("\nCentinela detenido.")

if __name__ == "__main__":
    if "--daemon" in sys.argv: daemon()
    else: pulse()
