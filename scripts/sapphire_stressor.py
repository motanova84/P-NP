#!/usr/bin/env python3
"""
🌀 QCAL Sapphire Stressor — Generador de datos VNA con perfiles térmicos
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.0
f₀ = 141.7001 Hz

Simula perfiles de temperatura controlados (adiabático, step_shock)
y genera archivos .DAT con respuesta lorentziana acoplada a la temperatura.
Permite testear fallos de control (LOST LOCK) en el orquestador.
"""
import numpy as np
import os
import time
import math

def generate_stressed_vna_data(output_path, profile_type="adiabatic",
                                f0_nominal=141.7001, q_nominal=1.18e9):
    """Simula perfiles térmicos y genera datos de barrido de frecuencia."""
    os.makedirs(os.path.dirname(output_path) or '.', exist_ok=True)
    num_points = 101
    span = 0.001
    frequencies = np.linspace(f0_nominal - span/2, f0_nominal + span/2, num_points)
    alpha_t = -2e-6
    timestamp_base = time.time()

    if profile_type == "adiabatic":
        temperatures = [4.20015 + 1e-5 * math.sin(i / 10.0) for i in range(num_points)]
    elif profile_type == "step_shock":
        temperatures = [4.20015 if i < 50 else 4.25000 for i in range(num_points)]
    else:
        temperatures = [4.20015] * num_points

    lines = [
        f"# FILENAME: SAPPHIRE_STRESS_{profile_type.upper()}.DAT\n",
        "# INSTRUMENT: VNA SIMULATOR (STOCHASTIC NOISE ENGINE)\n",
        f"# PROFILE TYPE: {profile_type.upper()}\n",
        "# ----------------------------------------------------------------------\n",
        f"# START TIMESTAMP: {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}\n",
        "# [START OF DATA]\n",
        "# Timestamp(s), Temp_K, Freq_Hz, S21_Mag_dB, S21_Phase_rad\n"
    ]

    np.random.seed(42)
    for i, f in enumerate(frequencies):
        T = temperatures[i]
        delta_T = T - 4.20015
        f0_effective = f0_nominal + (alpha_t * delta_T)
        detuning = (f - f0_effective) / f0_effective
        s21_complex = 1.0 / (1.0 + 2j * q_nominal * detuning)
        magnitude_db = 20 * np.log10(np.abs(s21_complex) + 1e-4) + np.random.normal(0, 0.05)
        phase_rad = np.angle(s21_complex) + np.random.normal(0, 0.01)
        ts = timestamp_base + (i * 0.02)
        lines.append(f"{ts:.3f}, {T:.6f}, {f:.8f}, {magnitude_db:.3f}, {phase_rad:.4f}\n")

    grad_medio = (temperatures[-1] - temperatures[0]) / (num_points * 0.02)
    f_final_peak = f0_nominal + (alpha_t * (temperatures[np.argmax(temperatures)] - 4.20015))

    lines.append("# [END OF DATA]\n")
    lines.append("# ----------------------------------------------------------------------\n")
    lines.append(f"# Center Frequency (f0): {f_final_peak:.8f} Hz\n")
    lines.append(f"# Loaded Q-Factor: {q_nominal:.2e}\n")
    lines.append(f"# Mean Thermal Gradient: {grad_medio:.6f} K/s\n")
    lines.append("Status: LOGGED\n")

    with open(output_path, "w") as f:
        f.writelines(lines)

    print(f"✅ Datos de estrés [{profile_type}] → {output_path}")
    print(f"   f₀ = {f_final_peak:.8f} Hz | Q = {q_nominal:.2e}")
    print(f"   Gradiente térmico medio: {grad_medio:.6f} K/s")
    return profile_type, grad_medio

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="QCAL Sapphire Stressor")
    parser.add_argument("--output", default="data/RESONATOR_SCAN_STRESS.DAT")
    parser.add_argument("--profile", default="adiabatic",
                        choices=["adiabatic", "step_shock", "stable"])
    args = parser.parse_args()
    generate_stressed_vna_data(args.output, profile_type=args.profile)
