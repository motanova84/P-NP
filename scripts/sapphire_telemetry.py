#!/usr/bin/env python3
"""
🌀 QCAL Sapphire Telemetry — Puente VNA → Validación Lean 4
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.0
f₀ = 141.7001 Hz

Lee el buffer del Analizador de Redes Vectorial (VNA) y el termómetro
de Óxido de Rutenio, calcula Q y desviación, exporta estado unificado.
"""
import json, os, time, sys

def read_instrument_buffer(file_path):
    """Lee el buffer del VNA y del termómetro de Óxido de Rutenio."""
    if not os.path.exists(file_path):
        raise FileNotFoundError(f"No se encontró el archivo de datos en: {file_path}")

    with open(file_path, 'r') as f:
        lines = f.readlines()

    data_points = []
    metadata = {}

    for line in lines:
        if line.startswith('#'):
            if "Center Frequency" in line:
                try:
                    metadata["f0_measured"] = float(line.split(":")[-1].strip().split()[0])
                except: pass
            elif "Loaded Q-Factor" in line:
                try:
                    q_str = line.split(":")[-1].strip()
                    metadata["q_factor"] = float(q_str.replace('e', 'e'))
                except: pass
            continue

        parts = line.strip().split(',')
        if len(parts) == 5:
            try:
                data_points.append({
                    "timestamp": float(parts[0]),
                    "temp_k": float(parts[1]),
                    "freq_hz": float(parts[2]),
                    "s21_db": float(parts[3]),
                    "phase_rad": float(parts[4])
                })
            except: pass

    return metadata, data_points

def process_telemetry(input_path, output_json):
    try:
        meta, points = read_instrument_buffer(input_path)
        if not points:
            print("❌ No se encontraron datos en el archivo.")
            return

        peak_point = max(points, key=lambda p: p["s21_db"])
        f_target = 141.7001
        drift = peak_point["freq_hz"] - f_target
        abs_drift = abs(drift)
        is_coherent = abs_drift < 1e-6
        coherence_value = max(0.0, 1.0 - abs_drift / 1e-4)

        telemetry_status = {
            "telemetry_metadata": {
                "source_file": input_path,
                "processed_at": time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                "version": "1.1"
            },
            "environment": {
                "temperature_k": round(peak_point["temp_k"], 6),
                "frequency_hz": round(peak_point["freq_hz"], 8),
                "q_factor": meta.get("q_factor", 0.0)
            },
            "control_metrics": {
                "phase_drift_hz": round(drift, 10),
                "calculated_coherence": round(coherence_value, 8),
                "system_lock": "ACTIVE" if is_coherent else "LOST",
                "drift_within_tolerance": is_coherent
            }
        }

        os.makedirs(os.path.dirname(output_json) or '.', exist_ok=True)
        with open(output_json, 'w') as jf:
            json.dump(telemetry_status, jf, indent=2)

        print(f"✅ Telemetría procesada correctamente → {output_json}")
        print(f"   Freq: {telemetry_status['environment']['frequency_hz']} Hz | "
              f"Drift: {drift:.2e} Hz | Lock: {telemetry_status['control_metrics']['system_lock']}")
        return telemetry_status

    except Exception as e:
        print(f"❌ Error: {str(e)}")
        return None

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="QCAL Sapphire Telemetry")
    parser.add_argument("--input", default="measurements/RESONATOR_SCAN_20260520_0405.dat",
                        help="Archivo de datos del instrumento")
    parser.add_argument("--output", default="config/sapphire_state.json",
                        help="Archivo JSON de salida")
    args = parser.parse_args()
    process_telemetry(args.input, args.output)
