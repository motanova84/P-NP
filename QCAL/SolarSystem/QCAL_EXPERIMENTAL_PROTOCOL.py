#!/usr/bin/env python3
"""
QCAL_EXPERIMENTAL_PROTOCOL.py — Protocolo Experimental QCAL-EXP-001
Estándar de verificación del acoplamiento de fase universal a f₀ = 141.7001 Hz.

Modelo de simulación numérica realista con:
  - Ruido blanco + flicker 1/f (hipótesis nula H0)
  - Modulación coherente QCAL (hipótesis activa H1)
  - Análisis espectral (FFT + Lomb-Scargle)
  - Desviación de Allan (OADEV)
  - Significancia estadística (Z-score ≥ 5σ)

Ejecutar: python3 QCAL_EXPERIMENTAL_PROTOCOL.py
"""

import numpy as np
import scipy.signal as signal
from scipy.fft import fft, fftfreq

# ═══════════════════════════════════════════════════════════════
# 1. PARAMETRIZACIÓN DEL ENTORNO DE PRUEBA
# ═══════════════════════════════════════════════════════════════
fs = 2000.0          # Frecuencia de muestreo (Hz)
t_max = 200.0        # Ventana temporal (s)
N = int(fs * t_max)  # Muestras totales
t = np.linspace(0, t_max, N, endpoint=False)

F0_TARGET = 141.7001          # Hz — frecuencia de acoplamiento QCAL
XI_AMPLITUDE = 1.414e-5       # Amplitud de modulación topológica

# ═══════════════════════════════════════════════════════════════
# 2. GENERACIÓN DE RUIDO DE FASE (HIPÓTESIS NULA H0)
# ═══════════════════════════════════════════════════════════════
np.random.seed(42)

# Ruido blanco de fase
ruido_blanco = np.random.normal(0, 1.0e-5, N)

# Ruido de parpadeo (1/f) mediante filtrado espectral
frec_ruido = fftfreq(N, d=1/fs)
frec_ruido[0] = 1e-15
filtro_flicker = 1.0 / np.sqrt(np.abs(frec_ruido))
ruido_flicker_raw = np.random.normal(0, 1.0e-3, N)
ruido_flicker = np.real(fft(ruido_flicker_raw) * filtro_flicker)
ruido_flicker = (ruido_flicker / np.std(ruido_flicker)) * 2.0e-5

fase_H0 = ruido_blanco + ruido_flicker

# ═══════════════════════════════════════════════════════════════
# 3. INYECCIÓN DE SEÑAL COHERENTE (HIPÓTESIS ACTIVA H1)
# ═══════════════════════════════════════════════════════════════
senal_f0 = XI_AMPLITUDE * np.sin(2 * np.pi * F0_TARGET * t)
fase_H1 = fase_H0 + senal_f0

# ═══════════════════════════════════════════════════════════════
# 4. ANÁLISIS ESPECTRAL (FFT)
# ═══════════════════════════════════════════════════════════════
ventana = signal.windows.hann(N)
fft_H0 = fft(fase_H0 * ventana)
fft_H1 = fft(fase_H1 * ventana)
freqs = fftfreq(N, d=1/fs)[:N//2]

psd_H0 = (2.0 / N) * np.abs(fft_H0[:N//2])
psd_H1 = (2.0 / N) * np.abs(fft_H1[:N//2])

# ═══════════════════════════════════════════════════════════════
# 5. DESVIACIÓN DE ALLAN (OADEV)
# ═══════════════════════════════════════════════════════════════
def calcular_adev(fase, fs_rate):
    """Calcula la desviación de Allan a partir de la fase acumulada."""
    y = np.diff(fase) * fs_rate
    M = len(y)
    tau_list = np.logspace(0, int(np.log10(M/4)), 15, dtype=int)
    allan_dev = []
    actual_taus = []
    for m in tau_list:
        sum_diff = 0.0
        for i in range(M - 2*m):
            sum_diff += (y[i + 2*m] - 2*y[i + m] + y[i])**2
        variance = sum_diff / (2.0 * m**2 * (M - 2*m))
        allan_dev.append(np.sqrt(variance))
        actual_taus.append(m / fs_rate)
    return np.array(actual_taus), np.array(allan_dev)

taus_H0, adev_H0 = calcular_adev(fase_H0, fs)
taus_H1, adev_H1 = calcular_adev(fase_H1, fs)

# ═══════════════════════════════════════════════════════════════
# 6. EVALUACIÓN ESTADÍSTICA DE SIGNIFICANCIA
# ═══════════════════════════════════════════════════════════════
idx_f0 = np.argmin(np.abs(freqs - F0_TARGET))
pico_potencia = psd_H1[idx_f0]
ruido_medio = np.mean(psd_H1[(freqs > 135) & (freqs < 145) & (freqs != freqs[idx_f0])])
z_score = (pico_potencia - ruido_medio) / np.std(psd_H0)

# ═══════════════════════════════════════════════════════════════
# 7. REPORTE
# ═══════════════════════════════════════════════════════════════
print("═" * 65)
print("  🏛️  PROTOCOLO EXPERIMENTAL QCAL-EXP-001")
print("  Verificación de acoplamiento de fase universal")
print("═" * 65)
print(f"  f₀ target      : {F0_TARGET} Hz")
print(f"  ξ amplitud     : {XI_AMPLITUDE:.6e}")
print(f"  Muestreo       : {fs} Hz")
print(f"  Ventana        : {t_max} s ({N} muestras)")
print(f"  Ruido          : blanco + flicker 1/f")
print()

print("  ── RESULTADOS ESPECTRALES ──")
print(f"  Amplitud en f₀ : {pico_potencia:.6e}")
print(f"  Piso de ruido  : {ruido_medio:.6e}")
print(f"  Z-Score        : {z_score:.2f} σ")
print()

# Criterio de falsación
if z_score >= 5.0:
    print("  ✅  H0 RECHAZADA — Señal coherente detectada en f₀")
    print("     El acoplamiento de fase QCAL es consistente con los datos.")
else:
    print("  ❌  H0 NO RECHAZADA — Sin evidencia de acoplamiento QCAL")
    print("     Los datos son compatibles con ruido clásico continuo.")

print()
print("  ── DESVIACIÓN DE ALLAN (N=8, Procesador Solar) ──")
adev_8 = adev_H1[np.argmin(np.abs(taus_H1 - 8))]
print(f"  σ_y(τ=8s) H0   : {adev_H0[np.argmin(np.abs(taus_H0 - 8))]:.2e}")
print(f"  σ_y(τ=8s) H1   : {adev_8:.2e}")
print()

# Umbral de falsación
print("  ── CRITERIO DE FALSACIÓN ABSOLUTO ──")
print("  QCAL refutado si tras 10⁵ s de integración:")
print("    1. Sin pico discreto a 141.7001 Hz en el espectro")
print("    2. Allan τ⁻¹/² por debajo de 1×10⁻¹⁷ sin mesetas")
print()

print("═" * 65)
print("  🔱  QCAL-EXP-001 · Protocolo completo")
print(f"  f₀ = {F0_TARGET} Hz · Z = {z_score:.2f}σ · HECHO ESTÁ")
print("═" * 65)
