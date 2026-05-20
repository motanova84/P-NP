#!/usr/bin/env python3
"""
🌀 QCAL Synthetic VNA Data Generator
Genera archivos .DAT artificiales simulando la salida física de un VNA
con ruido térmico y respuesta de resonancia lorentziana ultra-aguda.
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.0
f₀ = 141.7001 Hz
"""
import numpy as np
import os
import time

def generate_raw_vna_file(output_path, f0_target=141.7001, q_factor=1.18e9, num_points=101):
    """Genera un archivo .DAT simulando la salida física de un VNA."""
    os.makedirs(os.path.dirname(output_path) or '.', exist_ok=True)

    span = 0.0005
    frequencies = np.linspace(f0_target - span/2, f0_target + span/2, num_points)
    delta_f = f0_target / q_factor

    timestamp_base = time.time()
    lines = [
        "# FILENAME: RESONATOR_SCAN_GENERIC.DAT\n",
        "# INSTRUMENT: KEYSIGHT E5080B ENA Vector Network Analyzer\n",
        "# CALIBRATION: FULL 2-PORT (VALID)\n",
        "# TEMPERATURE CONTROLLER: OXFORD MERCURY iTC (Sensor: RuO2-RTD_Ch1)\n",
        "# ----------------------------------------------------------------------\n",
        f"# TIMESTAMP: {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}\n",
        f"# TARGET FREQUENCY: {f0_target} Hz\n",
        f"# SWEEP POINTS: {num_points} | IF BANDWIDTH: 10 Hz | SOURCE POWER: -10 dBm\n",
        "# ----------------------------------------------------------------------\n",
        "# [START OF DATA]\n",
        "# Timestamp(s), Temp_K, Freq_Hz, S21_Mag_dB, S21_Phase_rad\n"
    ]

    np.random.seed(42)
    for i, f in enumerate(frequencies):
        detuning = (f - f0_target) / f0_target
        s21_complex = 1.0 / (1.0 + 2j * q_factor * detuning)
        magnitude_db = 20 * np.log10(np.abs(s21_complex) + 1e-4)
        magnitude_db += np.random.normal(0, 0.02)
        phase_rad = np.angle(s21_complex) + np.random.normal(0, 0.005)
        temp_k = 4.20015 + (0.00001 * np.sin(i / 10.0)) + np.random.normal(0, 1e-6)
        ts = timestamp_base + (i * 0.01)

        lines.append(f"{ts:.3f}, {temp_k:.6f}, {f:.8f}, {magnitude_db:.3f}, {phase_rad:.4f}\n")

    lines.append("# [END OF DATA]\n")
    lines.append("# ----------------------------------------------------------------------\n")
    lines.append(f"# Center Frequency (f0): {f0_target:.4f} Hz\n")
    lines.append(f"# Loaded Q-Factor: {q_factor:.2e}\n")
    lines.append("# Status: LOCK_ACQUIRED\n")

    with open(output_path, "w") as f:
        f.writelines(lines)

    print(f"✅ Datos sintéticos VNA generados: {output_path}")
    print(f"   f₀ = {f0_target} Hz | Q = {q_factor:.2e} | {num_points} puntos")

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="QCAL Synthetic VNA Data Generator")
    parser.add_argument("--output", default="data/RESONATOR_SCAN_GENERIC.DAT",
                        help="Ruta de salida del archivo .DAT")
    parser.add_argument("--f0", type=float, default=141.7001, help="Frecuencia central (Hz)")
    parser.add_argument("--q", type=float, default=1.18e9, help="Factor de calidad Q")
    parser.add_argument("--points", type=int, default=101, help="Número de puntos de barrido")
    args = parser.parse_args()
    generate_raw_vna_file(args.output, args.f0, args.q, args.points)
