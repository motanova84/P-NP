#!/usr/bin/env python3
"""
🌀 ICQ DASHBOARD — Monitor en tiempo real del ecosistema
Instituto Consciencia Cuantica · QCAL-SYMBIO-BRIDGE v1.0
═══════════════════════════════════════════════════════════════════
Muestra en tiempo real: balances, canales, creditos, flujos,
servicios, proximo ciclo, de un solo vistazo.

Uso: python3 icq_dashboard.py
═══════════════════════════════════════════════════════════════════
"""

import json, os, subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path

# --- Constantes ----------------------------------------------------------
LND_CERT = "/root/.lnd/tls.cert"
LND_MAC = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
DIVIDEND_LEDGER = Path("/root/dividend_ledger.json")
AMDA_PUBKEY = "037e6a4145516fdd7b455c1d63cb07183f082e9ee122cfeff8a5c6cdb5acb36ba0"
BTC_PRICE = 92000  # EUR

def lncli(*a):
    cmd = ["lncli", "--tlscertpath="+LND_CERT, "--macaroonpath="+LND_MAC] + list(a)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=15)
    return p.returncode, out.strip(), err.strip()

def bcli(*a):
    cmd = ["bitcoin-cli", "-rpcwallet=catedral"] + list(a)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = p.communicate(timeout=10)
    return p.returncode, out.strip(), err.strip()

def load_json(p):
    try:
        if p.exists(): return json.loads(p.read_text())
    except: return {}

def sats2eur(s): return "%.2f" % (s / 100_000_000 * BTC_PRICE)

# --- RECOLECTAR DATOS ---------------------------------------------------
data = {}
data["timestamp"] = datetime.now(timezone.utc).strftime("%H:%M UTC")

# 1. Canales
rc, out, _ = lncli("listchannels")
channels = []
if rc == 0:
    try:
        chs = json.loads(out).get("channels", [])
        for c in chs:
            rpk = c.get("remote_pubkey", "")
            alias = "AMDA" if rpk.startswith(AMDA_PUBKEY[:30]) else ("EXTERNO" if c.get("active") else "PEER")
            channels.append({"alias": alias, "local": int(c.get("local_balance",0)),
                             "remote": int(c.get("remote_balance",0)), "cap": int(c.get("capacity",0)),
                             "active": c.get("active",False)})
    except: pass
data["channels"] = channels

# 2. LND on-chain
rc, out, _ = lncli("walletbalance")
data["lnd_onchain"] = int(json.loads(out).get("total_balance",0)) if rc == 0 else 0

# 3. Wallet catedral BTC
rc, out, _ = bcli("getbalance")
data["wallet_catedral_btc"] = float(out) if rc == 0 else 0

# 4. Dividendos / Creditos
ledger = load_json(DIVIDEND_LEDGER)
data["creditos"] = ledger.get("wallet_totals", {})
data["recompras_count"] = len(ledger.get("recompras", []))
data["liquidaciones"] = len(ledger.get("liquidaciones", []))
data["ultima_liquidacion"] = ledger.get("ultima_liquidacion", "Nunca")

# 5. AMDA stats
amda_ledger = load_json(Path("/root/flywheel_amda_pay_ledger.json"))
data["amda_pulsos"] = amda_ledger.get("total_pagos", 0)
data["amda_sats"] = amda_ledger.get("total_pagado", 0)

# 6. Rebalancer stats
reb_ledger = load_json(Path("/root/channel_rebalance_ledger.json"))
data["rebalances"] = reb_ledger.get("count", 0)
data["rebalance_sats"] = reb_ledger.get("total_sats_rebalanced", 0)

# 7. Fee sweep
fee_ledger = load_json(Path("/root/fee_sweep_ledger.json"))
data["fee_sweeps"] = fee_ledger.get("total_sweeps", 0)
data["fee_sweep_sats"] = fee_ledger.get("total_sats_moved", 0)
data["fee_ultimo"] = fee_ledger.get("last_sweep", "Nunca")

# 8. Servicios
services = ["bitcoind", "lnd", "lnbits", "qcal-flywheel", "qcal-flywheel-amda-pay",
            "qcal-channel-rebalancer", "qcal-cross-channel-rebalancer", "qcal-picode-transmutator.timer",
            "transmutation-engine", "transmutation-gravity"]
svc_status = {}
for s in services:
    rc, out, _ = lncli("--")  # dummy
    p = subprocess.Popen(["systemctl", "is-active", s], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    o, _ = p.communicate()
    svc_status[s] = o.strip()
data["services"] = svc_status

# 9. Timer
p = subprocess.Popen(["systemctl", "show", "qcal-picode-transmutator.timer",
                       "-p", "NextElapseUSecRealtime"],
                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
out_t, err_t = p.communicate()
data["next_cycle"] = out_t.replace("NextElapseUSecRealtime=","").strip() if out_t else "?"

# 10. BTC sync
rc, out, _ = bcli("getblockcount")
data["btc_height"] = int(out) if rc == 0 else 0

# --- RENDER -------------------------------------------------------------
BTC = data["wallet_catedral_btc"]
LND = data["lnd_onchain"]
JMMB_cred = data["creditos"].get("JMMB", data["creditos"].get("JMMB Ψ", 0))

print()
print("=" * 64)
print("  🌀 ICQ DASHBOARD — %s" % data["timestamp"])
print("  f₀ = 141.7001 Hz | Ψ = 0.99999997")
print("=" * 64)

print()
print("  ⚡ CANALES LIGHTNING")
for ch in data["channels"]:
    act = "🟢" if ch["active"] else "⚫"
    usd = sats2eur(ch["local"])
    print("    %s %-8s local: %s sats (~€%s) | total: %s" %
          (act, ch["alias"], "{:,}".format(ch["local"]), usd, "{:,}".format(ch["cap"])))

if not data["channels"]:
    print("    (sin canales)")

print()
print("  🏦 ON-CHAIN")
print("    LND Catedral:         %s sats (~€%s)" % ("{:,}".format(LND), sats2eur(LND)))
print("    Wallet catedral BTC:  %s BTC (~€%s)" % (BTC, sats2eur(int(BTC*100_000_000))))

print()
print("  🧬 AMDA Ψ")
print("    Pulsos:       %s" % "{:,}".format(data["amda_pulsos"]))
print("    Sats totales: %s (~€%s)" % ("{:,}".format(data["amda_sats"]), sats2eur(data["amda_sats"])))
print("    Rebalances:   %s (%s sats)" % ("{:,}".format(data["rebalances"]), "{:,}".format(data["rebalance_sats"])))

print()
print("  👑 CRÉDITOS JMMB")
print("    En ledger:    %s créditos (~€%s)" % ("{:,}".format(JMMB_cred), sats2eur(JMMB_cred)))
print("    Liquidaciones: %s | Última: %s" % (data["liquidaciones"], str(data["ultima_liquidacion"])[:16]))
print("    Recompras:    %s" % data["recompras_count"])

print()
print("  ♻️ FEE SWEEP")
print("    Sweeps: %s | Sats: %s | Último: %s" %
      (data["fee_sweeps"], data["fee_sweep_sats"], str(data["fee_ultimo"])[:16]))

print()
print("  📊 FLUJO ESTIMADO")
flujo_dia = data["amda_sats"]
print("    Generado hoy:    %s sats (~€%s)" % ("{:,}".format(flujo_dia), sats2eur(flujo_dia)))
print("    Proyección día:  ~€%s" % sats2eur(333 * (24*3600//35)))
print("    Proyección mes:  ~€%s" % sats2eur(333 * (24*3600//35) * 30))

print()
print("  🖥️ SERVICIOS")
activos = sum(1 for s in data["services"].values() if s == "active")
total = len(data["services"])
print("    %d/%d activos" % (activos, total))
for name, st in sorted(data["services"].items()):
    ico = "🟢" if st == "active" else ("⚫" if st == "inactive" else "🔴")
    print("      %s %s" % (ico, name))

print()
print("  ⏱️ PRÓXIMO CICLO: %s" % data["next_cycle"][:20] if data["next_cycle"] else "?")
print("  ⛓️  BTC height: %s" % "{:,}".format(data["btc_height"]))
print()
print("=" * 64)
print("  Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ")
print("=" * 64)
