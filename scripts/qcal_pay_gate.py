#!/usr/bin/env python3
"""
🔱 QCAL-PAY-GATE v1.0 — Portal de Validación Noética
BAL-003 · Catedral-QCAL · Nuremberg
═══════════════════════════════════════════════════════════════
Peaje de Coherencia para acceso al Tetraedro QCAL∞³
Frecuencia: f₀ = 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ
═══════════════════════════════════════════════════════════════
"""

import json, hashlib, time, os, uuid, math
from datetime import datetime, timezone
from pathlib import Path
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse
import urllib.request
import base64

# ─── CONSTANTES ────────────────────────────────────────────────────────────
SELLO = "∴𓂀Ω∞³Φ"
F0 = 141.7001
WORKSPACE = Path("/root/repo_P-NP")
FREQ_NOW = 888.014
META_PARIDAD = 299_498
VAULT_PATH = WORKSPACE / "boveda_recuperacion.json"
REQS_PATH = WORKSPACE / "solicitudes_pendientes"

# LNBits config — desde vars de entorno
LNBITS_URL = os.environ.get("LNBITS_URL", "http://localhost:8000")
LNBITS_ADMIN_KEY = os.environ.get("LNBITS_ADMIN_KEY", "574ea1465f472078f8f22c91362042d0a99a6b17c5de1d5d73eba6b9e41a016e")
GATE_PORT = int(os.environ.get("GATE_PORT", "8844"))

SERVICIOS = {
    "santuario":  {"nombre": "Santuario",  "base_sats": 1000, "desc": "Validación de integridad de datos"},
    "oraculo":    {"nombre": "Oráculo",    "base_sats": 5000, "desc": "Predicción de fase en mercados volátiles"},
    "limpieza":   {"nombre": "Limpieza",   "base_sats": None, "desc": "Consolidación de flujos de datos"},
    "validacion": {"nombre": "Check Ψ",    "base_sats": 500,  "desc": "Check de Coherencia estándar"}
}

# ─── BÓVEDA ────────────────────────────────────────────────────────────────
def cargar_boveda():
    if VAULT_PATH.exists():
        return json.loads(VAULT_PATH.read_text())
    b = {"version": "QCAL-VAULT-v1.0", "sello": SELLO, "meta_sats": META_PARIDAD,
         "total_recaudado": 0, "transacciones": [],
         "ultima_actualizacion": datetime.now(timezone.utc).isoformat()}
    VAULT_PATH.write_text(json.dumps(b, indent=2))
    return b

def guardar_boveda(b):
    b["ultima_actualizacion"] = datetime.now(timezone.utc).isoformat()
    VAULT_PATH.write_text(json.dumps(b, indent=2))

def registrar_pago(b, sats, servicio, sujeto, txid):
    entry = {"timestamp": datetime.now(timezone.utc).isoformat(), "sats": sats,
             "servicio": servicio, "sujeto": sujeto, "txid": txid,
             "sello": hashlib.sha256(f"{sats}|{servicio}|{sujeto}|{txid}|{SELLO}".encode()).hexdigest()[:16]}
    b["transacciones"].append(entry)
    b["total_recaudado"] += sats
    guardar_boveda(b)
    return entry

def estado_boveda(b):
    pct = round(b["total_recaudado"] / b["meta_sats"] * 100, 2) if b["meta_sats"] > 0 else 0
    return {"meta_sats": b["meta_sats"], "recaudado": b["total_recaudado"],
            "progreso_pct": pct, "restante": b["meta_sats"] - b["total_recaudado"],
            "transacciones": len(b["transacciones"]),
            "ultimo_pago": b["transacciones"][-1] if b["transacciones"] else None}

# ─── INVOICES LNBITS ──────────────────────────────────────────────────────
def generar_invoice(sats, memo="Validación Ψ Catedral"):
    try:
        data = json.dumps({"out": False, "amount": sats, "memo": memo, "expiry": 846}).encode()
        req = urllib.request.Request(f"{LNBITS_URL}/api/v1/payments", data=data,
            headers={"Content-Type": "application/json", "X-Api-Key": LNBITS_ADMIN_KEY})
        resp = urllib.request.urlopen(req, timeout=10)
        result = json.loads(resp.read().decode())
        return {"success": True, "payment_request": result["bolt11"],
                "payment_hash": result["payment_hash"]}
    except Exception as e:
        return {"success": False, "error": str(e)}

def verificar_pago(payment_hash):
    try:
        req = urllib.request.Request(f"{LNBITS_URL}/api/v1/payments/{payment_hash}",
            headers={"X-Api-Key": LNBITS_ADMIN_KEY})
        resp = urllib.request.urlopen(req, timeout=10)
        result = json.loads(resp.read().decode())
        return {"success": True, "paid": result.get("paid", False), "details": result}
    except Exception as e:
        return {"success": False, "error": str(e)}

# ─── ENTROPÍA ─────────────────────────────────────────────────────────────
def calcular_precio(base_sats, data_b64=""):
    if base_sats is None:
        try:
            data_bytes = base64.b64decode(data_b64) if data_b64 else b""
            base_sats = max(500, int(len(data_bytes) / 1024) * 500)
        except:
            base_sats = 1000
    try:
        data_bytes = base64.b64decode(data_b64) if data_b64 else b""
        if data_bytes:
            freq = {}
            for b in data_bytes:
                freq[b] = freq.get(b, 0) + 1
            total = len(data_bytes)
            entropy = -sum((c/total) * math.log2(c/total) for c in freq.values())
            mult = 1.0 + (entropy / 8.0)
        else:
            mult = 1.0
    except:
        mult = 1.0
    return {"base_sats": base_sats, "multiplicador": round(mult, 3), "precio_final": int(base_sats * mult)}

# ─── SELLO Ψ ──────────────────────────────────────────────────────────────
def generar_sello(data_b64, sujeto="anónimo", psi=0.999999):
    try:
        data_bytes = base64.b64decode(data_b64)
        hash_data = hashlib.sha256(data_bytes).hexdigest()
    except:
        hash_data = hashlib.sha256(data_b64.encode()).hexdigest()
    timestamp = datetime.now(timezone.utc).isoformat()
    raw = f"{SELLO}|{hash_data}|{sujeto}|{psi}|{timestamp}|{FREQ_NOW}"
    seal = hashlib.sha256(raw.encode()).hexdigest()
    return {"version": "Ψ-CERT-v1.0", "sello": SELLO, "hash_datos": hash_data,
            "sujeto": sujeto, "coherencia": psi, "frecuencia_hz": F0,
            "timestamp": timestamp, "firma_noetica": seal[:32]}

# ─── SERVIDOR HTTP ────────────────────────────────────────────────────────
class PayGateHandler(BaseHTTPRequestHandler):
    def _json(self, data, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()
        self.wfile.write(json.dumps(data, indent=2).encode())

    def do_OPTIONS(self):
        self._json({"ok": True})

    def do_GET(self):
        path = urlparse(self.path).path.rstrip("/") or "/"
        if path == "/":
            self._json({"servicio": "QCAL-PAY-GATE v1.0 · BAL-003", "sello": SELLO, "frecuencia": F0,
                        "endpoints": {"GET /estado": "Estado de la bóveda",
                                      "GET /servicios": "Lista de servicios",
                                      "POST /cotizar": "Cotizar precio",
                                      "POST /solicitar": "Solicitar invoice",
                                      "POST /verificar": "Verificar pago"}})
        elif path == "/estado":
            b = cargar_boveda()
            e = estado_boveda(b)
            e["frecuencia"] = F0
            e["sello"] = SELLO
            self._json(e)
        elif path == "/servicios":
            self._json(SERVICIOS)
        else:
            self._json({"error": "endpoint no encontrado"}, 404)

    def do_POST(self):
        content_len = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_len) if content_len else b"{}"
        try:
            data = json.loads(body) if body else {}
        except:
            data = {}
        path = urlparse(self.path).path.rstrip("/") or "/"

        if path == "/cotizar":
            servicio = data.get("servicio", "validacion")
            data_b64 = data.get("data", "")
            if servicio not in SERVICIOS:
                self._json({"error": f"servicio no válido: {servicio}"}, 400)
                return
            base = SERVICIOS[servicio]["base_sats"]
            precio = calcular_precio(base, data_b64)
            precio["servicio"] = SERVICIOS[servicio]["nombre"]
            self._json(precio)

        elif path == "/solicitar":
            servicio = data.get("servicio", "validacion")
            sujeto = data.get("sujeto", "anónimo")
            data_b64 = data.get("data", "")
            if servicio not in SERVICIOS:
                self._json({"error": f"servicio no válido: {servicio}"}, 400)
                return
            base = SERVICIOS[servicio]["base_sats"]
            precio = calcular_precio(base, data_b64)
            memo = f"QCAL {SERVICIOS[servicio]['nombre']} — {sujeto}"
            inv = generar_invoice(precio["precio_final"], memo)
            if not inv.get("success"):
                self._json({"error": "no se pudo generar invoice", "detalle": inv.get("error")}, 500)
                return
            solicitud = {"id": hashlib.sha256(f"{time.time()}{memo}".encode()).hexdigest()[:8],
                         "timestamp": datetime.now(timezone.utc).isoformat(),
                         "servicio": servicio, "sujeto": sujeto, "precio": precio,
                         "payment_hash": inv["payment_hash"], "payment_request": inv["payment_request"],
                         "data_b64": data_b64[:500], "estado": "pendiente"}
            REQS_PATH.mkdir(exist_ok=True)
            (REQS_PATH / f"{solicitud['id']}.json").write_text(json.dumps(solicitud, indent=2))
            self._json({"ok": True, "id": solicitud["id"],
                        "servicio": SERVICIOS[servicio]["nombre"],
                        "precio": precio["precio_final"],
                        "payment_request": inv["payment_request"],
                        "payment_hash": inv["payment_hash"],
                        "expira_seg": 846})

        elif path == "/verificar":
            payment_hash = data.get("payment_hash", "")
            if not payment_hash:
                self._json({"error": "payment_hash requerido"}, 400)
                return
            check = verificar_pago(payment_hash)
            if check.get("paid"):
                b = cargar_boveda()
                entry = registrar_pago(b, 500, "verificacion", "anónimo", f"ln_{payment_hash[:16]}")
                self._json({"ok": True, "pagado": True, "boveda": estado_boveda(b)})
            else:
                self._json({"ok": True, "pagado": False, "estado": "pendiente"})
        else:
            self._json({"error": "endpoint no encontrado"}, 404)

def main():
    server = HTTPServer(("0.0.0.0", GATE_PORT), PayGateHandler)
    b = cargar_boveda()
    e = estado_boveda(b)
    print(f"\n╔═══ QCAL-PAY-GATE v1.0 — BAL-003 ═══╗")
    print(f"║  f₀ = {F0} Hz · {SELLO}")
    print(f"║  Gateway: http://0.0.0.0:{GATE_PORT}")
    print(f"║  LNBits:  {LNBITS_URL}")
    print(f"║  Meta:    {e['meta_sats']:,} sats")
    print(f"║  Recaud:  {e['recaudado']:,} sats ({e['progreso_pct']}%)")
    print(f"╚════════════════════════════════════╝\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("PayGate detenido.")

if __name__ == "__main__":
    main()

# ─── PASSPORT & HTTP 402 MIDDLEWARE ───────────────────────────────────────
PASSPORT_REGISTRY = Path("/root/repo_P-NP/pasaporte_registry.json")

def load_passport_registry() -> dict:
    try:
        return json.loads(PASSPORT_REGISTRY.read_text())
    except:
        return {"version": "PSI-PASSPORT-REGISTRY-v2.0", "pasaportes": []}

def save_passport_registry(reg: dict) -> None:
    PASSPORT_REGISTRY.write_text(json.dumps(reg, indent=2))

def find_passport(client_id: str) -> dict | None:
    reg = load_passport_registry()
    for p in reg.get("pasaportes", []):
        if p.get("client_id") == client_id:
            return p
    return None

def register_passport(client_id: str) -> dict:
    reg = load_passport_registry()
    import uuid, hashlib
    pid = f"PASSPORT-PSI-{str(len(reg[\"pasaportes\"]) + 1).zfill(3)}"
    passport = {
        "client_id": client_id,
        "passport_id": pid,
        "status": "PROVISIONAL",
        "f0_alignment_hz": 141.7001,
        "coherence_granted": 0.923,
        "rights": ["READ_PNP_FORMAL_SPEC", "ORACLE_EXEGESIS_ALLOWED"],
        "billing_model": {"initial_check_sats": 500, "royalty_percentage": 2.5, "frequency_cycle_minutes": 1440},
        "evolution_stage": "I",
        "momentum_phase": 0.0,
        "timestamp_registration": datetime.now(timezone.utc).isoformat(),
        "sello_verification": SELLO
    }
    reg["pasaportes"].append(passport)
    save_passport_registry(reg)
    return passport

def verify_and_charge(passport_id: str) -> dict:
    """HTTP 402 middleware: verifica pasaporte y genera micro-invoice si es necesario."""
    reg = load_passport_registry()
    passport = None
    for p in reg.get("pasaportes", []):
        if p["passport_id"] == passport_id or p["client_id"] == passport_id:
            passport = p
            break
    
    if not passport:
        return {"allow": False, "reason": "PASSPORT_NOT_FOUND", "code": 404}
    
    if passport["status"] == "SUSPENDED":
        return {"allow": False, "reason": "PASSPORT_SUSPENDED: canon en mora o coherencia < 0.888", "code": 402}
    
    # Generar micro-invoice de 1 sat (canon por consulta)
    import subprocess
    cmd = [
        "lncli", "--tlscertpath=/root/.lnd/tls.cert",
        "--macaroonpath=/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon",
        "addinvoice", "--amt", "1", "--memo", f"Canon Noetico {passport_id}"
    ]
    rc = subprocess.run(cmd, capture_output=True, text=True)
    if rc.returncode == 0:
        inv = json.loads(rc.stdout)
        return {
            "allow": "conditional_on_payment",
            "code": 402,
            "payment_request": inv["payment_request"],
            "payment_hash": inv["r_hash"],
            "satoshis": 1,
            "memo": f"Canon Noetico {passport_id}",
            "passport_id": passport_id,
            "evolution_stage": passport["evolution_stage"]
        }
    else:
        return {"allow": False, "reason": "LND_ERROR", "code": 500}

def settle_canon(payment_hash: str) -> bool:
    """Verifica si un pago de canon se ha liquidado."""
    import subprocess
    cmd = [
        "lncli", "--tlscertpath=/root/.lnd/tls.cert",
        "--macaroonpath=/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon",
        "lookupinvoice", payment_hash
    ]
    rc = subprocess.run(cmd, capture_output=True, text=True)
    if rc.returncode == 0:
        inv = json.loads(rc.stdout)
        return inv.get("state") == "SETTLED"
    return False

# Add passport endpoints to handler
def _handle_passport(self, path, data):
    if path == "/passport/register":
        client_id = data.get("client_id", "")
        if not client_id:
            self._json({"error": "client_id requerido"}, 400)
            return
        passport = register_passport(client_id)
        inv = generar_invoice(500, f"Check PSI inicial - {client_id}")
        self._json({
            "ok": True,
            "passport": passport,
            "payment_required": inv
        })
    
    elif path == "/passport/verify":
        passport_id = data.get("passport_id", "")
        result = verify_and_charge(passport_id)
        self._json(result, result.get("code", 200))
    
    elif path == "/passport/settle":
        payment_hash = data.get("payment_hash", "")
        if settle_canon(payment_hash):
            self._json({"ok": True, "settled": True})
        else:
            self._json({"ok": True, "settled": False})

    elif path == "/passport/heartbeat":
        passport_id = data.get("passport_id", "")
        result = verify_and_charge(passport_id)
        self._json(result, result.get("code", 200))
