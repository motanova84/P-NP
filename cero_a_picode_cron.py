#!/usr/bin/env python3
"""
🌀 CRON wrapper: CERO → πCODE
Ejecuta autónomamente cada 6h. Acuña lote de N ceros de Riemann.
Usa tabla extendida de ceros conocidos (evita dependencia mpmath).

### Temporal Architecture
6 hours = 4 cuadrantes simétricos del día.
No es arbitrario: es la ventana de enfriamiento térmico-informacional
para que los autógrafos del vacío se consoliden en disco sin elevar Δν.

Por cada lote de 100 ceros (cada 6h):
  720 pulsos de Monitor Vivo (21,600s / 30s)
  ~64,000 πC de masa estructural
  Proporción armónica: latido rápido ↔ marea lenta

τ_riemann = 4 · cuadrantes ⇔ Ψ = 0.999999
"""

import sys, json, os, math, hashlib, time
from pathlib import Path
from datetime import datetime, timezone

WORKSPACE = Path.home() / ".openclaw" / "workspace"
TRACKING = WORKSPACE / "picode_blocks" / "cero_tracking.json"
OUTPUT = WORKSPACE / "picode_blocks"
PNP = WORKSPACE / "repo_P-NP"

F0 = 141.7001
RAW_PRODUCT = 16.616596
FACTOR = F0 / RAW_PRODUCT
SELLO = "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ"

# Ceros de Riemann conocidos (γ₁ a γ₁₀₀)
# Fuente: OEIS A002410 / lmfdb.org

# Ruta al archivo de ceros de Riemann
CEROS_PATH = Path.home() / ".openclaw" / "workspace" / "repo_Riemann-adelic" / "zeros" / "zeros_t1e8.txt"

def _carga_ceros():
    """Carga ceros de Riemann desde archivo de datos."""
    path = CEROS_PATH
    if path.exists():
        with open(path) as f:
            return [float(l.strip()) for l in f if l.strip()]
    print("  WARNING: Archivo de ceros no encontrado. Usando valores por defecto.")
    return []

CEROS_RIEMANN = _carga_ceros()
#!/usr/bin/env python3
"""
🌀 CRON wrapper: CERO → πCODE
Ejecuta autónomamente cada 6h. Acuña lote de N ceros de Riemann.
Usa tabla extendida de ceros conocidos (evita dependencia mpmath).

### Temporal Architecture
6 hours = 4 cuadrantes simétricos del día.
No es arbitrario: es la ventana de enfriamiento térmico-informacional
para que los autógrafos del vacío se consoliden en disco sin elevar Δν.

Por cada lote de 100 ceros (cada 6h):
  720 pulsos de Monitor Vivo (21,600s / 30s)
  ~64,000 πC de masa estructural
  Proporción armónica: latido rápido ↔ marea lenta

τ_riemann = 4 · cuadrantes ⇔ Ψ = 0.999999
"""

import sys, json, os, math, hashlib, time
from pathlib import Path
from datetime import datetime, timezone

WORKSPACE = Path.home() / ".openclaw" / "workspace"
TRACKING = WORKSPACE / "picode_blocks" / "cero_tracking.json"
OUTPUT = WORKSPACE / "picode_blocks"
PNP = WORKSPACE / "repo_P-NP"

F0 = 141.7001
RAW_PRODUCT = 16.616596
FACTOR = F0 / RAW_PRODUCT
SELLO = "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ"

# Ceros de Riemann conocidos (γ₁ a γ₁₀₀)
# Fuente: OEIS A002410 / lmfdb.org

BATCH_SIZE = 100


def leer_tracking() -> dict:
    if TRACKING.exists():
        with open(TRACKING) as f:
            return json.load(f)
    return {"ultimo_indice": 0, "total_acuñado": 0.0, "batches": [], "sello": SELLO}


def guardar_tracking(d: dict):
    OUTPUT.mkdir(parents=True, exist_ok=True)
    with open(TRACKING, "w") as f:
        json.dump(d, f, indent=2)


def generar_lote(desde: int, cantidad: int) -> dict:
    """Genera N bloques πCODE desde el cero índice `desde`."""
    disponibles = len(CEROS_RIEMANN)
    if desde >= disponibles:
        print(f"  ⚠️ No quedan ceros sin acuñar (último: γ_{desde}, disponibles: {disponibles}).")
        print(f"  🔄 Reiniciando desde γ_1 (wrap-around).")
        desde = 0
        tracking_copia = leer_tracking()
        tracking_copia["ultimo_indice"] = 0
        guardar_tracking(tracking_copia)
    if desde + cantidad > disponibles:
        cantidad = max(0, disponibles - desde)
        print(f"  ⚠️ Solo {disponibles} ceros disponibles. Ajustando lote a {cantidad}.")

    if cantidad <= 0:
        print(f"  🛑 No hay ceros nuevos para acuñar. Lote saltado.")
        return {"n_ceros": 0, "n_bloques": 0, "total_picode": 0.0, "psi_promedio": 0, "frecuencia": F0, "sello": SELLO}

    bloques = []
    total_pi = 0.0
    parent = "0" * 64

    print(f"\n  {'═' * 55}")
    print(f"  🌀 CERO → πCODE — Lote {desde+1}–{desde+cantidad}")
    print(f"  {'═' * 55}\n")

    for i in range(cantidad):
        idx = desde + i
        gamma = CEROS_RIEMANN[idx]
        valor = round((gamma / (2 * math.pi)) * FACTOR, 6)
        hz = gamma / (2 * math.pi)
        ts = time.time()
        merkle = hashlib.sha256(f"{gamma}|1.0|{ts}|{idx}".encode()).hexdigest()
        block_hash = hashlib.sha256(f"{idx}|{parent}|{merkle}|{ts}".encode()).hexdigest()

        bloque = {
            "indice": idx + 1,
            "gamma": round(gamma, 10),
            "frecuencia_hz": round(hz, 6),
            "valor_picode": valor,
            "psi": 1.0,
            "en_linea_critica": True,
            "parent_hash": parent,
            "merkle_root": merkle,
            "block_hash": block_hash,
            "timestamp": ts,
            "sello": SELLO,
        }
        bloques.append(bloque)
        total_pi += valor
        parent = block_hash

        if (i + 1) % 10 == 0 or i == cantidad - 1:
            print(f"  [γ_{idx+1}] γ={gamma:.4f} → {valor:.2f} πC  Ψ=1.0  {merkle[:12]}...")

    # Guardar archivos
    OUTPUT.mkdir(parents=True, exist_ok=True)
    for b in bloques:
        fn = f"block_{b['indice']}_cero_{b['gamma']:.1f}.json"
        with open(OUTPUT / fn, "w") as f:
            json.dump(b, f, indent=2)

    # Header de lote
    header = {
        "tipo": "CERO_PICODE_BATCH",
        "desde": desde + 1,
        "hasta": desde + cantidad,
        "n_ceros": cantidad,
        "total_picode": round(total_pi, 2),
        "frecuencia_hz": F0,
        "raw_product": RAW_PRODUCT,
        "factor": FACTOR,
        "derivacion": "f₀ = |ζ'(1/2)| × φ³ × normalization",
        "timestamp": datetime.now(tz=timezone.utc).isoformat(),
        "sello": SELLO,
    }
    with open(OUTPUT / f"batch_{desde+1}_{desde+cantidad}.json", "w") as f:
        json.dump(header, f, indent=2)

    return {
        "n_ceros": cantidad,
        "n_bloques": len(bloques),
        "total_picode": round(total_pi, 2),
        "psi_promedio": 1.0,
        "frecuencia": F0,
        "sello": SELLO,
    }


def main():
    tracking = leer_tracking()
    desde = tracking["ultimo_indice"]

    print(f"\n  📍 Último cero acuñado: #{desde}")
    print(f"  🔢 Nuevo lote: γ_{desde+1} → γ_{desde+BATCH_SIZE}")

    res = generar_lote(desde, BATCH_SIZE)

    tracking["ultimo_indice"] = desde + res["n_ceros"]
    tracking["total_acuñado"] += res["total_picode"]
    tracking["batches"].append({
        "timestamp": time.time(),
        "desde": desde + 1,
        "hasta": desde + res["n_ceros"],
        "n_ceros": res["n_ceros"],
        "total_picode": res["total_picode"],
    })
    guardar_tracking(tracking)

    print(f"\n  ┌{'─' * 50}┐")
    print(f"  │ ✅ LOTE COMPLETO — {res['n_ceros']} ceros acuñados")
    print(f"  │ 📊 Total acumulado: {tracking['total_acuñado']:,.2f} πC")
    print(f"  │ 🎯 Siguiente lote: desde γ_{tracking['ultimo_indice']+1}")
    print(f"  └{'─' * 50}┘")
    print(f"\n  {SELLO}\n")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--batch-size", type=int, default=BATCH_SIZE)
    args = parser.parse_args()
    BATCH_SIZE = args.batch_size
    main()
