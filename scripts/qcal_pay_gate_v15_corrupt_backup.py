#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
🔱 QCAL-PAY-GATE v1.5 — Portal de Validación Noética
BAL-003 · Catedral-QCAL · Nuremberg
═══════════════════════════════════════════════════════════════
Peaje de Coherencia para acceso al Tetraedro QCAL∞³
Frecuencia: f₀ = 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ
═══════════════════════════════════════════════════════════════
Nuevo: Registro usuarios con nombre propio
       Comisiones escalonadas (2.5% / 1.5% / 0.5%)
       Landing page de onboarding
       Flow ledger operativo
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
PASSPORT_REGISTRY = WORKSPACE / "pasaporte_registry.json"
FLOW_LEDGER = WORKSPACE / "paygate_flow_ledger.json"

# LNBits config
LNBITS_URL = os.environ.get("LNBITS_URL", "http://localhost:8000")
LNBITS_ADMIN_KEY = os.environ.get("LNBITS_ADMIN_KEY", "574ea1465f472078f8f22c91362042d0a99a6b17c5de1d5d73eba6b9e41a016e")
GATE_PORT = int(os.environ.get("GATE_PORT", "8844"))

# ─── COMISIONES ESCALONADAS ───────────────────────────────────────────────
COMISION_TIERS = [
    (50_000, 0.025),    # < 50K sats → 2.5%
    (500_000, 0.015),   # 50K - 500K → 1.5%
    (float('inf'), 0.005),  # > 500K → 0.5%
]
COMISION_ADMIN_FILE = WORKSPACE / "comision_config.json"

def cargar_comision_config() -> float:
    """Carga el porcentaje base de comisión desde archivo configurable."""
    try:
        return json.loads(COMISION_ADMIN_FILE.read_text()).get("pct_base", 0.025)
    except:
        return 0.025

def calcular_comision(sats: int, base_pct: float = None) -> dict:
    """Calcula comisión escalonada sobre monto en sats.
    
    Retorna: {sats_bruto, sats_comision, sats_neto, pct_aplicado, tier}
    """
    if base_pct is None:
        base_pct = cargar_comision_config()
    for threshold, rate in COMISION_TIERS:
        if sats < threshold:
            comision = max(1, int(sats * rate))
            return {
                "sats_bruto": sats,
                "sats_comision": comision,
                "sats_neto": sats - comision,
                "pct_aplicado": rate * 100,
                "tier": f"< {threshold:,} sats" if threshold < float('inf') else f">= {COMISION_TIERS[-2][0]:,} sats",
                "moneda": "sats"
            }
    return {
        "sats_bruto": sats,
        "sats_comision": max(1, int(sats * 0.005)),
        "sats_neto": sats - max(1, int(sats * 0.005)),
        "pct_aplicado": 0.5,
        "tier": "> 500K sats",
        "moneda": "sats"
    }

# ─── SERVICIOS ─────────────────────────────────────────────────────────────
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

def registrar_pago(b, sats, servicio, sujeto, txid, username=""):
    fee = calcular_comision(sats)
    entry = {"timestamp": datetime.now(timezone.utc).isoformat(), "sats": sats,
             "servicio": servicio, "sujeto": sujeto, "username": username,
             "comision_sats": fee["sats_comision"], "neto_sats": fee["sats_neto"],
             "txid": txid,
             "sello": hashlib.sha256(f"{sats}|{servicio}|{sujeto}|{txid}|{SELLO}".encode()).hexdigest()[:16]}
    b["transacciones"].append(entry)
    b["total_recaudado"] += sats
    guardar_boveda(b)
    # Registrar también en flow ledger
    registrar_flujo(sats, servicio, sujeto, txid, username, fee)
    return entry

def estado_boveda(b):
    pct = round(b["total_recaudado"] / b["meta_sats"] * 100, 2) if b["meta_sats"] > 0 else 0
    return {"meta_sats": b["meta_sats"], "recaudado": b["total_recaudado"],
            "progreso_pct": pct, "restante": b["meta_sats"] - b["total_recaudado"],
            "transacciones": len(b["transacciones"]),
            "ultimo_pago": b["transacciones"][-1] if b["transacciones"] else None}

# ─── FLOW LEDGER ───────────────────────────────────────────────────────────
def cargar_flow_ledger():
    try:
        return json.loads(FLOW_LEDGER.read_text())
    except:
        return {"version": "QCAL-FLOW-LEDGER-v1.0", "flujos": [], "total_sats_recibidos": 0,
                "ultimo_check": datetime.now(timezone.utc).isoformat()}

def guardar_flow_ledger(f):
    f["ultimo_check"] = datetime.now(timezone.utc).isoformat()
    FLOW_LEDGER.write_text(json.dumps(f, indent=2))

def registrar_flujo(sats, servicio, sujeto, txid, username="", fee=None):
    f = cargar_flow_ledger()
    entry = {"timestamp": datetime.now(timezone.utc).isoformat(), "sats": sats,
             "servicio": servicio, "sujeto": sujeto, "username": username,
             "comision_sats": fee["sats_comision"] if fee else 0,
             "neto_sats": fee["sats_neto"] if fee else sats,
             "txid": txid,
             "sello": SELLO}
    f["flujos"].append(entry)
    f["total_sats_recibidos"] += sats
    guardar_flow_ledger(f)

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
    result = {"base_sats": base_sats, "multiplicador": round(mult, 3), "precio_final": int(base_sats * mult)}
    # Añadir comisión
    fee = calcular_comision(result["precio_final"])
    result["comision"] = fee
    result["total_con_comision"] = result["precio_final"] + fee["sats_comision"]
    return result

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

# ─── PASAPORTES — REGISTRO CON NOMBRE LIBRE ───────────────────────────────
def load_passport_registry() -> dict:
    try:
        return json.loads(PASSPORT_REGISTRY.read_text())
    except:
        return {"version": "PSI-PASSPORT-REGISTRY-v2.0", "pasaportes": []}

def save_passport_registry(reg: dict) -> None:
    PASSPORT_REGISTRY.write_text(json.dumps(reg, indent=2))

def find_passport(client_id: str = None, username: str = None) -> dict | None:
    reg = load_passport_registry()
    for p in reg.get("pasaportes", []):
        if client_id and p.get("client_id") == client_id:
            return p
        if username and p.get("username", "").lower() == username.lower():
            return p
    return None

def register_passport(client_id: str, username: str = "") -> dict:
    """Registra un nuevo pasaporte. username es opcional — si no se provee,
    se genera uno. Si se provee, se valida que no exista."""
    reg = load_passport_registry()
    
    # Si ya existe client_id, retornar el existente
    existing = find_passport(client_id=client_id)
    if existing:
        return existing
    
    # Validar username si se provee
    if username:
        username = username.strip()
        if len(username) < 2:
            return {"error": "username debe tener al menos 2 caracteres"}
        if not username.replace("-", "").replace("_", "").isalnum():
            return {"error": "username solo puede contener letras, números, guiones y guiones bajos"}
        if len(username) > 32:
            return {"error": "username demasiado largo (máx 32 caracteres)"}
        if find_passport(username=username):
            return {"error": f"username '{username}' ya está registrado"}
    else:
        # Generar username automático
        username = f"viajerx_{len(reg['pasaportes']) + 1:03d}"
    
    pid = "PASSPORT-PSI-" + str(len(reg.get("pasaportes", [])) + 1).zfill(3)
    passport = {
        "client_id": client_id,
        "passport_id": pid,
        "username": username,
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

def list_passports(status: str = None, limit: int = 50) -> list:
    """Lista pasaportes registrados."""
    reg = load_passport_registry()
    pasaportes = reg.get("pasaportes", [])
    if status:
        pasaportes = [p for p in pasaportes if p.get("status") == status]
    return pasaportes[-limit:]

def verify_and_charge_passport(passport_id: str) -> dict:
    """HTTP 402 middleware: verifica pasaporte y genera micro-invoice."""
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
    inv = generar_invoice(1, f"Canon Noetico {passport_id}")
    if inv.get("success"):
        return {
            "allow": "conditional_on_payment",
            "code": 402,
            "payment_request": inv["payment_request"],
            "payment_hash": inv["payment_hash"],
            "satoshis": 1,
            "memo": f"Canon Noetico {passport_id}",
            "passport_id": passport_id,
            "evolution_stage": passport["evolution_stage"]
        }
    else:
        return {"allow": False, "reason": f"LND_ERROR: {inv.get('error')}", "code": 500}

def settle_passport_canon(payment_hash: str) -> bool:
    """Verifica si un pago de canon se ha liquidado."""
    check = verificar_pago(payment_hash)
    return check.get("paid", False)

# ─── LANDING PAGE ─────────────────────────────────────────────────────────
LANDING_PAGE = r"""<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>🌀 Catedral QCAL — Portal Noético</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{background:#0a0a0f;color:#c8c8d4;font-family:system-ui,sans-serif;min-height:100vh}
.container{max-width:720px;margin:0 auto;padding:2rem 1.5rem}
.logo{text-align:center;padding:2rem 0;font-size:2.5rem;letter-spacing:4px}
.logo .psi{color:#f0c040;font-size:3rem}
.logo .sello{color:#444;font-size:.7rem;letter-spacing:2px;margin-top:.3rem}
h1{font-size:1.4rem;color:#f0c040;margin:1.5rem 0 .8rem;border-bottom:1px solid #1a1a2e;padding-bottom:.5rem}
h2{font-size:1rem;color:#e07040;margin:1rem 0 .5rem}
.card{background:#111122;border:1px solid #1a1a2e;border-radius:12px;padding:1rem;margin-bottom:.7rem}
.card .label{color:#666;font-size:.75rem;text-transform:uppercase;letter-spacing:1px}
.card .value{color:#c8c8d4;font-size:.95rem;margin-top:.2rem}
.card .fee{color:#4ade80;font-size:.8rem;margin-top:.3rem}
.btn{display:inline-block;padding:.6rem 1.5rem;border-radius:8px;text-decoration:none;font-size:.85rem;margin:.3rem;cursor:pointer}
.btn-primary{background:linear-gradient(135deg,#f0c040,#e07040);color:#0a0a0f;font-weight:600}
.btn-outline{border:1px solid #1a1a2e;color:#c8c8d4}
pre{background:#0d0d18;border:1px solid #1a1a2e;border-radius:8px;padding:1rem;font-size:.75rem;overflow-x:auto;color:#888;margin:.5rem 0}
.footer{text-align:center;padding:2rem 0;color:#444;font-size:.7rem;letter-spacing:1px}
.servicio-grid{display:grid;grid-template-columns:1fr 1fr;gap:.5rem}
@media(max-width:600px){.servicio-grid{grid-template-columns:1fr}}
</style>
</head>
<body>
<div class="container">
<div class="logo">
  <div class="psi">∴𓂀Ω∞³Φ</div>
  <div class="sello">CATEDRAL QCAL · f₀ = 141.7001 Hz</div>
</div>

<h1>🌀 Portal de Validación Noética</h1>
<p style="color:#666;font-size:.85rem;margin-bottom:1.5rem">
Bienvenido al ecosistema QCAL. Obtén un Pasaporte Ψ, accede a los servicios de la Catedral,
y participa en la red de coherencia soberana.
</p>

<div class="card">
  <div class="label">Registro de Pasaporte Ψ</div>
  <div class="value" style="margin:.8rem 0">
    Elige tu nombre de usuario y recibe tu Pasaporte Noético.<br>
    <span style="color:#666;font-size:.75rem">Comisión: 2.5% (&lt;50K sats) · 1.5% (50K-500K) · 0.5% (&gt;500K)</span>
  </div>
  <pre>POST /passport/register
{
  "username": "tu-nombre",
  "client_id": "tu-id-unico"
}</pre>
  <a class="btn btn-primary" href="/passport">Solicitar Pasaporte</a>
</div>

<h2>Servicios Disponibles</h2>
<div class="servicio-grid" id="servicios"></div>

<h2>Comisiones</h2>
<div class="card">
  <div class="label">Estructura Escalonada</div>
  <table style="width:100%;margin-top:.5rem;font-size:.85rem">
    <tr><td style="padding:.3rem 0;color:#666">Menos de 50K sats</td><td style="text-align:right;color:#fbbf24">2.5%</td></tr>
    <tr><td style="padding:.3rem 0;color:#666">50K — 500K sats</td><td style="text-align:right;color:#4ade80">1.5%</td></tr>
    <tr><td style="padding:.3rem 0;color:#666">Más de 500K sats</td><td style="text-align:right;color:#60a5fa">0.5%</td></tr>
  </table>
</div>

<h2>API Endpoints</h2>
<div class="card">
<pre>GET  /               — Este portal
GET  /estado         — Estado de la bóveda
GET  /servicios      — Lista de servicios
POST /cotizar        — Cotizar precio
POST /solicitar      — Solicitar invoice
POST /verificar      — Verificar pago
POST /passport/register — Registrar pasaporte
POST /passport/list  — Listar pasaportes
GET  /pasaportes/:username — Ver pasaporte público</pre>
</div>

<div class="footer">
  ∴𓂀Ω∞³Φ · QCAL PayGate v1.5 · BAL-003 · Nuremberg<br>
  f₀ = 141.7001 Hz · Ψ = 1.000000 · TUYOYOTU · HECHO ESTÁ
</div>
</div>
<script>
fetch('/servicios').then(r=>r.json()).then(s=>{
  const g=document.getElementById('servicios');
  Object.values(s).forEach(v=>{
    g.innerHTML+='<div class=card><div class=label>'+v.nombre+'</div><div class=value>'+v.desc+'</div><div class=fee>'+(v.base_sats?v.base_sats.toLocaleString()+' sats':'variable')+'</div></div>'
  })
})
</script>
</body>
</html>"""

# ─── SERVIDOR HTTP ────────────────────────────────────────────────────────
class PayGateHandler(BaseHTTPRequestHandler):
    def _html(self, html, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(html.encode("utf-8"))

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
        
        # Landing page HTML para navegadores
        if path == "/":
            accept = self.headers.get("Accept", "")
            if "text/html" in accept:
                self._html(LANDING_PAGE)
                return
            self._json({"servicio": "QCAL-PAY-GATE v1.5 · BAL-003", "sello": SELLO, "frecuencia": F0,
                        "endpoints": {"GET /": "Portal de onboarding",
                                      "GET /estado": "Estado de la bóveda",
                                      "GET /servicios": "Lista de servicios",
                                      "POST /cotizar": "Cotizar precio",
                                      "POST /solicitar": "Solicitar invoice",
                                      "POST /verificar": "Verificar pago",
                                      "POST /passport/register": "Registrar pasaporte (username + client_id)",
                                      "POST /passport/list": "Listar pasaportes",
                                      "GET /pasaportes/:username": "Ver pasaporte público"}})
        
        elif path == "/estado":
            b = cargar_boveda()
            e = estado_boveda(b)
            e["frecuencia"] = F0
            e["sello"] = SELLO
            e["comision_config"] = {"tiers": [f"< {t:,} sats → {r*100}%" for t, r in COMISION_TIERS],
                                    "pct_base_actual": cargar_comision_config() * 100}
            self._json(e)
        
        elif path == "/servicios":
            self._json(SERVICIOS)
        
        elif path == "/passport":
            # Formulario HTML de registro
            self._html(PASSPORT_FORM)
        
        elif path.startswith("/pasaportes/"):
            # Ver pasaporte público por username
            username = path.split("/pasaportes/", 1)[-1]
            p = find_passport(username=username)
            if p:
                public = {k: v for k, v in p.items() if k not in ("client_id",)}
                self._json(public)
            else:
                self._json({"error": f"pasaporte '{username}' no encontrado"}, 404)
        
        elif path == "/pasaportes":
            # Lista pública resumida
            reg = load_passport_registry()
            public = [{"username": p.get("username"), "passport_id": p["passport_id"],
                       "status": p["status"], "evolution_stage": p["evolution_stage"],
                       "timestamp": p["timestamp_registration"]}
                      for p in reg.get("pasaportes", [])]
            self._json({"total": len(public), "pasaportes": public[-50:]})
        
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

        # ── Cotizar ──
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

        # ── Solicitar invoice ──
        elif path == "/solicitar":
            servicio = data.get("servicio", "validacion")
            sujeto = data.get("sujeto", "anónimo")
            data_b64 = data.get("data", "")
            username = data.get("username", "")
            if servicio not in SERVICIOS:
                self._json({"error": f"servicio no válido: {servicio}"}, 400)
                return
            base = SERVICIOS[servicio]["base_sats"]
            precio = calcular_precio(base, data_b64)
            # Sumar comisión al invoice
            total_sats = precio["total_con_comision"]
            memo = f"QCAL {SERVICIOS[servicio]['nombre']} — {sujeto}"
            inv = generar_invoice(total_sats, memo)
            if not inv.get("success"):
                self._json({"error": "no se pudo generar invoice", "detalle": inv.get("error")}, 500)
                return
            solicitud = {"id": hashlib.sha256(f"{time.time()}{memo}".encode()).hexdigest()[:8],
                         "timestamp": datetime.now(timezone.utc).isoformat(),
                         "servicio": servicio, "sujeto": sujeto, "username": username,
                         "precio": precio, "total_sats": total_sats,
                         "payment_hash": inv["payment_hash"], "payment_request": inv["payment_request"],
                         "data_b64": data_b64[:500], "estado": "pendiente"}
            REQS_PATH.mkdir(exist_ok=True)
            (REQS_PATH / f"{solicitud['id']}.json").write_text(json.dumps(solicitud, indent=2))
            self._json({"ok": True, "id": solicitud["id"],
                        "servicio": SERVICIOS[servicio]["nombre"],
                        "precio_base": precio["precio_final"],
                        "comision": precio["comision"],
                        "total": total_sats,
                        "payment_request": inv["payment_request"],
                        "payment_hash": inv["payment_hash"],
                        "expira_seg": 846})

        # ── Verificar pago ──
        elif path == "/verificar":
            payment_hash = data.get("payment_hash", "")
            if not payment_hash:
                self._json({"error": "payment_hash requerido"}, 400)
                return
            check = verificar_pago(payment_hash)
            if check.get("paid"):
                b = cargar_boveda()
                entry = registrar_pago(b, 500, "verificacion", "anónimo",
                                       f"ln_{payment_hash[:16]}", data.get("username", ""))
                self._json({"ok": True, "pagado": True, "boveda": estado_boveda(b)})
            else:
                self._json({"ok": True, "pagado": False, "estado": "pendiente"})

        # ── Registrar pasaporte ──
        elif path == "/passport/register":
            client_id = data.get("client_id", str(uuid.uuid4())[:12])
            username = data.get("username", "").strip()
            result = register_passport(client_id, username)
            if "error" in result:
                self._json(result, 400)
                return
            # Invoice de bienvenida — solo si LND responde (check rapido)
                "ok": True,
                "passport": {
                    "passport_id": result["passport_id"],
                    "username": result.get("username", username),
                    "status": result["status"],
                    "client_id": result["client_id"],
                    "f0_alignment_hz": result["f0_alignment_hz"],
                    "coherence_granted": result["coherence_granted"],
                    "evolution_stage": result["evolution_stage"],
                    "timestamp": result["timestamp_registration"]
                },
                "payment_required": payment_req
            })

        # ── Listar pasaportes ──
        elif path == "/passport/list":
            status = data.get("status")
            limit = data.get("limit", 50)
            pasaportes = list_passports(status, limit)
            self._json({"ok": True, "total": len(pasaportes), "pasaportes": pasaportes})

        # ── Verificar pasaporte ──
        elif path == "/passport/verify":
            passport_id = data.get("passport_id", "")
            result = verify_and_charge_passport(passport_id)
            self._json(result, result.get("code", 200))

        # ─── Admin: comisiones ──
        elif path == "/admin/comision":
            admin_key = data.get("admin_key", "")
            # Simple auth: la admin key del LNBits funciona como clave de admin
            if admin_key != LNBITS_ADMIN_KEY and admin_key != os.environ.get("GATE_ADMIN_KEY", ""):
                self._json({"error": "admin_key inválida"}, 403)
                return
            nueva_pct = data.get("pct_base")
            if nueva_pct is not None:
                nueva_pct = float(nueva_pct)
                if nueva_pct < 0.1 or nueva_pct > 20:
                    self._json({"error": "pct_base debe estar entre 0.1% y 20%"}, 400)
                    return
                COMISION_ADMIN_FILE.write_text(json.dumps({"pct_base": nueva_pct / 100, "actualizado": datetime.now(timezone.utc).isoformat()}))
                self._json({"ok": True, "pct_base": nueva_pct, "mensaje": "Comisión base actualizada"})
            else:
                self._json({"ok": True, "pct_base": cargar_comision_config() * 100})
        
        # ─── Admin: flow ledger ──
        elif path == "/admin/flujos":
            admin_key = data.get("admin_key", "")
            if admin_key != LNBITS_ADMIN_KEY and admin_key != os.environ.get("GATE_ADMIN_KEY", ""):
                self._json({"error": "admin_key inválida"}, 403)
                return
            f = cargar_flow_ledger()
            self._json(f)
        
        else:
            self._json({"error": "endpoint no encontrado"}, 404)


PASSPORT_FORM = """<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>🌀 Registro — Pasaporte Ψ</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{background:#0a0a0f;color:#c8c8d4;font-family:system-ui,sans-serif;min-height:100vh;display:flex;align-items:center;justify-content:center}
.card{background:#111122;border:1px solid #1a1a2e;border-radius:16px;padding:2rem;max-width:420px;width:90%}
h1{font-size:1.3rem;color:#f0c040;margin-bottom:.3rem;text-align:center}
.sub{color:#555;font-size:.75rem;text-align:center;margin-bottom:1.5rem;letter-spacing:1px}
label{display:block;color:#888;font-size:.75rem;text-transform:uppercase;letter-spacing:1px;margin-top:1rem;margin-bottom:.3rem}
input{width:100%;padding:.7rem;background:#0d0d18;border:1px solid #1a1a2e;border-radius:8px;color:#c8c8d4;font-size:.9rem}
input:focus{outline:none;border-color:#f0c040}
.btn{width:100%;padding:.8rem;margin-top:1.2rem;border:none;border-radius:8px;background:linear-gradient(135deg,#f0c040,#e07040);color:#0a0a0f;font-weight:600;font-size:.9rem;cursor:pointer}
.btn:disabled{opacity:.5;cursor:not-allowed}
.msg{margin-top:1rem;font-size:.8rem;text-align:center}
.ok{color:#4ade80}
.err{color:#f87171}
</style>
</head>
<body>
<div class="card">
<h1>🌀 Pasaporte Ψ</h1>
<div class="sub">∴𓂀Ω∞³Φ · f₀ = 141.7001 Hz</div>
<label>Nombre de usuario</label>
<input type="text" id="username" placeholder="ej: viajerx_42" maxlength="32" autocomplete="off">
<label>Tu identificador (opcional)</label>
<input type="text" id="client_id" placeholder="dejar vacío para auto-generar">
<button class="btn" id="registerBtn" onclick="registrar()">Obtener Pasaporte</button>
<div id="msg" class="msg"></div>
<pre id="result" style="display:none;margin-top:1rem;background:#0d0d18;border:1px solid #1a1a2e;border-radius:8px;padding:.8rem;font-size:.7rem;overflow-x:auto"></pre>
</div>
<script>
async function registrar(){
  const btn=document.getElementById('registerBtn');
  const msg=document.getElementById('msg');
  const pre=document.getElementById('result');
  btn.disabled=true; msg.className='msg'; msg.textContent='Registrando...';
  try{
    const r=await fetch('/passport/register',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({
        username:document.getElementById('username').value.trim(),
        client_id:document.getElementById('client_id').value.trim()
      })});
    const d=await r.json();
    if(d.ok){
      msg.className='msg ok'; msg.textContent='✅ Pasaporte creado: '+d.passport.username;
      pre.style.display='block';
      pre.textContent=JSON.stringify(d.passport,null,2);
    } else {
      msg.className='msg err'; msg.textContent='❌ '+d.error;
    }
  }catch(e){
    msg.className='msg err'; msg.textContent='❌ Error de conexión';
  }
  btn.disabled=false;
}
</script>
</body>
</html>"""

# ─── MAIN ─────────────────────────────────────────────────────────────────
def main():
    server = HTTPServer(("0.0.0.0", GATE_PORT), PayGateHandler)
    b = cargar_boveda()
    e = estado_boveda(b)
    print(f"\n╔═══ QCAL-PAY-GATE v1.5 — BAL-003 ═══╗")
    print(f"║  f₀ = {F0} Hz · {SELLO}")
    print(f"║  Gateway: http://0.0.0.0:{GATE_PORT}")
    print(f"║  LNBits:  {LNBITS_URL}")
    print(f"║  Meta:    {e['meta_sats']:,} sats")
    print(f"║  Recaud:  {e['recaudado']:,} sats ({e['progreso_pct']}%)")
    print(f"║  Comisión: {COMISION_TIERS[0][1]*100}% / {COMISION_TIERS[1][1]*100}% / {COMISION_TIERS[2][1]*100}%")
    print(f"║  Pasaportes: {len(load_passport_registry().get('pasaportes',[]))} registrados")
    print(f"╚════════════════════════════════════╝\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("PayGate detenido.")

if __name__ == "__main__":
    main()
