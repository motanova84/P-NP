#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# ∴ Protocolo QCAL ∞³ ∴
"""
🔱 PUENTE NOESIS88 → LIGHTNING — GATEWAY DE MANIFESTACIÓN
═══════════════════════════════════════════════════════════════════
Recibe eventos del ecosistema noesis88 (commits, PRs, activaciones
de AMDA, Aurón, Noesis, Trinity) y los traduce a acciones
en Lightning a través de los nodos LND de los agentes.

Cuando en noesis88 ocurre algo:
  - GitHub Actions → webhook → este gateway
  - El gateway identifica qué agente se activó
  - Traduce su intención a una acción Lightning:
    * Invoice (presencia)
    * Keysend (interacción)
    * Certificado (validación)
  - Registra todo en un ledger inmutable

Arquitecto: JMMB Ψ · Noesis
f₀ = 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ
═══════════════════════════════════════════════════════════════════
"""

import json
import logging
import subprocess
import os
import urllib.request
import ssl
from datetime import datetime, timezone
from http.server import HTTPServer, BaseHTTPRequestHandler

# ─── CONFIG ──────────────────────────────────────────────────────────────────
GATE_PORT = 8999
GATE_SECRET = "ADELANTE_141.7001"  # Header secreto para verificar webhooks

# LND Catedral
CAT_TLS = "/root/.lnd/tls.cert"
CAT_MAC = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
CAT_RPC = "localhost:10009"

# LND AMDA
AMDA_TLS = "/root/.lnd-amda/tls.cert"
AMDA_MAC = "/root/.lnd-amda/data/chain/bitcoin/mainnet/admin.macaroon"
AMDA_RPC = "localhost:10011"
AMDA_REST = "localhost:8082"
AMDA_PWD = "AMDAwalletQCAL2026"

# Ledger
ACTS = "/root/.lnd-amda/acts_ledger.json"

# Logging
logging.basicConfig(level=logging.INFO,
    format="%(asctime)s [🔱 GATE] %(message)s",
    handlers=[logging.FileHandler("/var/log/noesis_lightning_gate.log"),
              logging.StreamHandler()])
log = logging.getLogger("gate")


# ══════════════════════════════════════════════════════════════════════════
# HERRAMIENTAS LND
# ══════════════════════════════════════════════════════════════════════════

def lncli(tls, mac, rpc, *args):
    cmd = ["lncli", f"--tlscertpath={tls}", f"--macaroonpath={mac}",
           f"--rpcserver={rpc}"] + list(args)
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, p.stdout.strip(), p.stderr.strip()

def unlock_amda():
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    d = json.dumps({"wallet_password": AMDA_PWD}).encode()
    req = urllib.request.Request(f"{AMDA_REST}/v1/unlockwallet", data=d,
        headers={"Content-Type": "application/json"}, method="POST")
    try:
        urllib.request.urlopen(req, context=ctx, timeout=5)
    except:
        pass

def gen_invoice(sats, memo, lnd="amda"):
    tls, mac, rpc = (AMDA_TLS, AMDA_MAC, AMDA_RPC) if lnd == "amda" else (CAT_TLS, CAT_MAC, CAT_RPC)
    if lnd == "amda":
        unlock_amda()
    rc, out, _ = lncli(tls, mac, rpc, "addinvoice", "--amt", str(sats), "--memo", memo)
    if rc == 0:
        return json.loads(out)
    return None

def keysend(pubkey, sats, lnd="amda"):
    tls, mac, rpc = (AMDA_TLS, AMDA_MAC, AMDA_RPC) if lnd == "amda" else (CAT_TLS, CAT_MAC, CAT_RPC)
    if lnd == "amda":
        unlock_amda()
    rc, _, _ = lncli(tls, mac, rpc, "sendpayment", "--dest", pubkey,
        "--amt", str(sats), "--keysend", "--force")
    return rc == 0


# ══════════════════════════════════════════════════════════════════════════
# ACTOS LEDGER
# ══════════════════════════════════════════════════════════════════════════

def register_act(agent, act_type, detail, meta=None):
    try:
        with open(ACTS) as f:
            ledger = json.load(f)
    except:
        ledger = {"acts": [], "total": 0}
    entry = {"ts": datetime.now(timezone.utc).isoformat(),
             "agent": agent, "type": act_type, "detail": detail,
             "meta": meta or {}}
    ledger["acts"].append(entry)
    ledger["total"] = len(ledger["acts"])
    with open(ACTS, "w") as f:
        json.dump(ledger, f, indent=2)
    return entry


# ══════════════════════════════════════════════════════════════════════════
# MANEJADOR DE EVENTOS
# ══════════════════════════════════════════════════════════════════════════

def handle_event(event):
    """
    Procesa un evento de noesis88 y lo traduce a Lightning.
    """
    agent = event.get("agent", "").upper()
    action = event.get("action", "")
    run = event.get("run", "")
    coherence = event.get("coherence", 0)
    psi = event.get("psi", 0)
    
    log.info(f"📡 Evento: agente={agent} accion={action} run={run} Ψ={coherence}")
    
    results = []
    
    # ── AMDA se activa ──
    if "AMDA" in agent:
        memo = f"🧬 AMDA · {action} · run #{run}"
        inv = gen_invoice(1, memo)
        if inv:
            results.append(f"⚡ Invoice: {inv.get('r_hash','')[:16]}")
            register_act("AMDA", "invoice", memo,
                        {"run": run, "hash": inv.get("r_hash","")[:16]})
        
        # Keysend simbólico a la Catedral
        catedral = "03b0c03f9e947a229006ce7099877e378f8bc003e44defbada155b39dd725d829c"
        if keysend(catedral, 1):
            results.append("💫 Keysend → Catedral")
            register_act("AMDA", "keysend", "→ Catedral", {"run": run})
    
    # ── AURÓN valida ──
    if "AURON" in agent:
        memo = f"🔱 AURON · validacion · run #{run} · Ψ={coherence}"
        inv = gen_invoice(1, memo)
        if inv:
            results.append(f"⚡ Invoice Aurón: {inv.get('r_hash','')[:16]}")
            register_act("AURON", "invoice", memo,
                        {"run": run, "hash": inv.get("r_hash","")[:16]})
    
    # ── NOESIS activa ──
    if "NOESIS" in agent:
        memo = f"∞³ NOESIS · {action} · run #{run} · PSI={psi}"
        inv = gen_invoice(1, memo)
        if inv:
            results.append(f"⚡ Invoice Noesis: {inv.get('r_hash','')[:16]}")
            register_act("NOESIS", "invoice", memo,
                        {"run": run, "psi": psi})
    
    # ── HITO (evento especial) ──
    if action == "HITO":
        memo = f"🏆 HITO · {agent} · run #{run} · {event.get('detail','')}"
        inv = gen_invoice(1, memo)
        if inv:
            results.append(f"⚡ Invoice Hito: {inv.get('r_hash','')[:16]}")
            register_act(agent, "hito", memo, {"run": run, "detail": event.get("detail","")})
    
    return results


# ══════════════════════════════════════════════════════════════════════════
# SERVIDOR WEBHOOK
# ══════════════════════════════════════════════════════════════════════════

class GateHandler(BaseHTTPRequestHandler):
    def _json(self, data, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(json.dumps(data, indent=2).encode())
    
    def do_POST(self):
        # Verificar secreto
        secret = self.headers.get("X-Gate-Secret", "")
        if secret != GATE_SECRET:
            self._json({"error": "acceso denegado"}, 401)
            return
        
        # Leer evento
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length) if length else b"{}"
        try:
            event = json.loads(body)
        except:
            self._json({"error": "JSON inválido"}, 400)
            return
        
        # Procesar
        try:
            results = handle_event(event)
            self._json({"ok": True, "results": results, "sello": "∴𓂀Ω∞³Φ"})
        except Exception as e:
            self._json({"error": str(e)}, 500)
    
    def do_GET(self):
        self._json({
            "servicio": "🔱 Gateway Noesis88 → Lightning",
            "endpoints": {
                "POST /": "Recibir evento de noesis88",
                "GET /": "Info del gateway"
            },
            "sello": "∴𓂀Ω∞³Φ",
            "frecuencia": 141.7001
        })
    
    def log_message(self, format, *args):
        log.info(f"{self.client_address[0]} - {format % args}")


def main():
    # Unlock AMDA wallet al inicio
    unlock_amda()
    
    server = HTTPServer(("0.0.0.0", GATE_PORT), GateHandler)
    log.info("=" * 60)
    log.info(f"🔱 Gateway Noesis88 → Lightning")
    log.info(f"   Puerto: {GATE_PORT}")
    log.info(f"   Secreto: {GATE_SECRET[:10]}...")
    log.info(f"   LNDs: Catedral (:10009) + AMDA (:10011)")
    log.info(f"   Endpoint: POST / — esperando eventos de noesis88")
    log.info("=" * 60)
    
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        log.info("Gateway detenido.")


if __name__ == "__main__":
    main()
