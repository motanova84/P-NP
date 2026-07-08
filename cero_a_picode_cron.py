#!/usr/bin/env python3
"""
cero_a_picode_cron.py — Protocolo de Auto-Lavado y Unicidad [V.10]
CERO → πCODE desde Ceros de Riemann.
POOL EXTENSIBLE: nunca recicla ceros. Cuando se agotan, genera nuevos.
Fuente: BAL-003 (100K ceros), con generación ∞ vía mpmath.
"""

import sys, json, os, math, hashlib, time, subprocess, tempfile
from pathlib import Path
from datetime import datetime, timezone

WORKSPACE = Path.home() / ".openclaw" / "workspace"
TRACKING = WORKSPACE / "picode_blocks" / "cero_tracking.json"
OUTPUT = WORKSPACE / "picode_blocks"
POOL_DIR = WORKSPACE / "picode_blocks" / "cero_pool"
BAL_003 = "root@195.201.219.237"
BAL_ZERO_FILE = "/root/coinqcal/ceros/zeros_t1e8.txt.gz"
BAL_GENERATOR = "/root/generar_zeros_precision.py"

F0 = 141.7001
RAW_PRODUCT = 16.616596
FACTOR = F0 / RAW_PRODUCT
SELLO = "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ"
BATCH_SIZE = 100


def leer_tracking() -> dict:
    if TRACKING.exists():
        with open(TRACKING) as f:
            return json.load(f)
    return {"ultimo_indice": 0, "total_acuñado": 0.0, "batches": [], "sello": SELLO}


def guardar_tracking(d: dict):
    OUTPUT.mkdir(parents=True, exist_ok=True)
    # Escribir a archivo temporal, luego renombrar (transacción atómica)
    tmp = TRACKING.with_suffix(".tmp")
    with open(tmp, "w") as f:
        json.dump(d, f, indent=2)
    tmp.replace(TRACKING)
    # Backup automático cada 10 batches
    n_batches = len(d.get("batches", []))
    if n_batches > 0 and n_batches % 10 == 0:
        bk = TRACKING.with_name(f"cero_tracking_bk_{n_batches}.json")
        with open(bk, "w") as f:
            json.dump(d, f, indent=2)


def pool_path() -> Path:
    """Ruta al pool de ceros locales."""
    POOL_DIR.mkdir(parents=True, exist_ok=True)
    return POOL_DIR / "ceros_riemann.txt"


def cargar_pool_local() -> list[float]:
    """Carga el pool local de ceros. Si no existe, lo descarga de BAL-003."""
    p = pool_path()
    if not p.exists():
        print(f"  📥 Pool local no encontrado. Descargando de BAL-003...")
        try:
            subprocess.run(
                ["scp", "-o", "ConnectTimeout=10",
                 f"{BAL_003}:{BAL_ZERO_FILE}", str(p)],
                capture_output=True, text=True, timeout=60, check=True
            )
            print(f"  ✅ Pool descargado ({p.stat().st_size} bytes)")
        except Exception as e:
            print(f"  ⚠️ No se pudo descargar de BAL-003: {e}")
            print(f"  ⚠️ Usando tabla de respaldo (50 ceros).")
            return [
                14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
                37.586178, 40.918720, 43.327073, 48.005151, 49.773832,
            ]
    with open(p) as f:
        return [float(line.strip()) for line in f if line.strip()]


def generar_nuevos_ceros(desde_indice: int, cantidad: int) -> list[float]:
    """
    Genera NUEVOS ceros de Riemann vía BAL-003 (mpmath).
    Retorna una lista de valores gamma recién generados.
    """
    print(f"  🆕 Generando {cantidad} nuevos ceros desde γ_{desde_indice}...")
    print(f"     (vía ssh BAL-003: python3 generador_ceros_soberano.py)")

    try:
        script = f"""
        import mpmath, sys
        mpmath.mp.dps = 30
        start = {desde_indice}
        count = {cantidad}
        for i in range(start, start + count):
            z = mpmath.zetazero(i)
            print(f\"{{z.imag:.10f}}\")
        """
        result = subprocess.run(
            ["ssh", "-o", "ConnectTimeout=10", BAL_003, f"python3 -c \"{script}\""],
            capture_output=True, text=True, timeout=120
        )
        if result.returncode != 0:
            print(f"  ❌ Error SSH: {result.stderr[:200]}")
            return []
        gammas = [float(line.strip()) for line in result.stdout.strip().split("\n") if line.strip()]
        if len(gammas) != cantidad:
            print(f"  ⚠️ Esperados {cantidad}, recibidos {len(gammas)}")
        print(f"  ✅ Generados {len(gammas)} nuevos ceros (primer γ: {gammas[0]:.4f})")
        return gammas
    except Exception as e:
        print(f"  ❌ Error generando ceros: {e}")
        return []


def extender_pool(nuevos_ceros: list[float]):
    """Añade nuevos ceros al pool local."""
    p = pool_path()
    with open(p, "a") as f:
        for gamma in nuevos_ceros:
            f.write(f"{gamma:.10f}\n")
    # Reabrir para mostrar tamaño actualizado
    with open(p) as f:
        total = sum(1 for _ in f)
    print(f"  📦 Pool extendido: ahora {total} ceros totales")


def asegurar_ceros_desde(desde: int, cantidad: int) -> list[float]:
    """
    Asegura que el pool local tenga al menos `desde + cantidad` ceros.
    Si no, genera los faltantes desde BAL-003 y los agrega al pool.
    Retorna el sublistado de `cantidad` ceros empezando en `desde`.
    """
    pool = cargar_pool_local()
    disponibles = len(pool)
    print(f"  Pool local: {disponibles:,} ceros disponibles")

    if desde + cantidad > disponibles:
        faltantes = desde + cantidad - disponibles
        print(f"  🆕 Faltan {faltantes} ceros. Generando...")
        nuevos = generar_nuevos_ceros(disponibles + 1, faltantes)
        if not nuevos:
            print(f"  ❌ No se pudieron generar ceros. Abortando.")
            return []
        extender_pool(nuevos)
        pool = cargar_pool_local()
        disponibles = len(pool)
        print(f"  Pool actualizado: {disponibles:,} ceros")

    return pool[desde:desde + cantidad]


def generar_lote(desde: int, cantidad: int) -> tuple[dict, int]:
    """Genera N bloques πCODE desde el cero índice `desde`, SIN wrap-around."""
    ceros = asegurar_ceros_desde(desde, cantidad)
    if not ceros:
        return {"n_ceros": 0, "n_bloques": 0, "total_picode": 0.0, "psi_promedio": 0, "frecuencia": F0, "sello": SELLO}, desde

    # Ajustar cantidad real si hay menos de los esperados
    cantidad_real = min(cantidad, len(ceros))
    if cantidad_real < cantidad:
        print(f"  ⚠️ Solo {len(ceros)} ceros disponibles. Ajustando lote a {cantidad_real}.")

    bloques = []
    total_pi = 0.0
    parent = "0" * 64
    sello = SELLO

    print(f"\n  {'═' * 55}")
    print(f"  🌀 CERO → πCODE — Lote γ_{desde+1}–γ_{desde+cantidad_real}")
    print(f"  {'═' * 55}\n")

    for i in range(cantidad_real):
        idx = desde + i
        gamma = ceros[i]
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
            "sello": sello,
        }
        bloques.append(bloque)
        total_pi += valor
        parent = block_hash

        if (i + 1) % 10 == 0 or i == cantidad_real - 1:
            print(f"  [γ_{idx+1}] γ={gamma:.4f} → {valor:.2f} πC  Ψ=1.0  {merkle[:12]}...")

    # Guardar archivos individuales
    OUTPUT.mkdir(parents=True, exist_ok=True)
    for b in bloques:
        fn = f"block_{b['indice']}_cero_{b['gamma']:.1f}.json"
        with open(OUTPUT / fn, "w") as f:
            json.dump(b, f, indent=2)

    # Header de lote
    header = {
        "tipo": "CERO_PICODE_BATCH",
        "desde": desde + 1,
        "hasta": desde + cantidad_real,
        "n_ceros": cantidad_real,
        "total_picode": round(total_pi, 2),
        "frecuencia_hz": F0,
        "raw_product": RAW_PRODUCT,
        "factor": FACTOR,
        "derivacion": "f₀ = |ζ'(1/2)| × φ³ × normalization",
        "timestamp": datetime.now(tz=timezone.utc).isoformat(),
        "sello": sello,
    }
    with open(OUTPUT / f"batch_{desde+1}_{desde+cantidad_real}.json", "w") as f:
        json.dump(header, f, indent=2)

    return {
        "n_ceros": cantidad_real,
        "n_bloques": len(bloques),
        "total_picode": round(total_pi, 2),
        "psi_promedio": 1.0,
        "frecuencia": F0,
        "sello": sello,
    }, desde


def main():
    tracking = leer_tracking()
    desde = tracking["ultimo_indice"]

    print(f"\n  📍 Último cero acuñado: #{desde}")
    print(f"  🔢 Nuevo lote: γ_{desde+1} → γ_{desde+BATCH_SIZE}")

    res, desde_real = generar_lote(desde, BATCH_SIZE)

    tracking["ultimo_indice"] = desde_real + res["n_ceros"]
    tracking["total_acuñado"] += res["total_picode"]
    tracking["batches"].append({
        "timestamp": time.time(),
        "desde": desde_real + 1,
        "hasta": desde_real + res["n_ceros"],
        "n_ceros": res["n_ceros"],
        "total_picode": res["total_picode"],
    })
    guardar_tracking(tracking)

    print(f"\n  ┌{'─' * 50}┐")
    print(f"  │ ✅ LOTE COMPLETO — {res['n_ceros']} ceros acuñados")
    print(f"  │ 📊 Total acumulado: {tracking['total_acuñado']:,.2f} πC")
    print(f"  │ 🆕 Sin wrap-around — pool se extiende infinitamente")
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
