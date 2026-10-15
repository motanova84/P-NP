"""
Vibro-Fluorescence QCAL Experimental Framework
===============================================

Implementación del marco teórico-físico para experimentos de acoplamiento
vibro-fluorescente bajo campo QCAL Ψ.

Este módulo implementa:
1. Ecuación maestra del acoplamiento vibro-fluorescente
2. Formalismo espectral para diseño experimental
3. Modelo dinámico de resonancia proteica
4. Transducción a fluorescencia
5. Predicciones cuantitativas QCAL
6. Controles de falsación críticos

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import numpy as np
import math
from typing import Tuple, Dict, List, Callable
from scipy import signal, fft
from scipy.stats import f as f_distribution


# ==================== CONSTANTES UNIVERSALES ====================

# Frecuencia portadora QCAL (Hz)
OMEGA_0_QCAL = 141.7001  # Hz

# Umbral de coherencia crítico
PSI_CRITICO = 0.888

# Constante κ_Π
KAPPA_PI = 2.578208

# Razón áurea
PHI = (1 + math.sqrt(5)) / 2

# Armónicos resonantes de Magicicada
MAGICICADA_HARMONICS = [1, 2, 3, 13, 17]


# ==================== I. ECUACIÓN MAESTRA DEL ACOPLAMIENTO ====================

class VibroFluorescentCoupling:
    """
    Hamiltoniano total del acoplamiento vibro-fluorescente.
    
    H_total = H_proteína + H_campo + H_acoplamiento
    """
    
    def __init__(self, mu: float = 1.0, Q: float = 0.1, chi2: float = 0.01, chi3: float = 0.001):
        """
        Parámetros del acoplamiento.
        
        Args:
            mu: Dipolo eléctrico de transición electrónica
            Q: Cuadrupolo + acoplamiento vibracional
            chi2: Coeficiente no lineal de segundo orden χ⁽²⁾
            chi3: Coeficiente no lineal de tercer orden χ⁽³⁾
        """
        self.mu = mu
        self.Q = Q
        self.chi2 = chi2
        self.chi3 = chi3
    
    def H_acoplamiento(self, E: float, grad_E: float) -> float:
        """
        Calcula el Hamiltoniano de acoplamiento.
        
        H_acoplamiento = μ·E + Q:∇E + χ⁽²⁾E² + χ⁽³⁾E³ + ...
        
        Args:
            E: Campo eléctrico
            grad_E: Gradiente del campo eléctrico
            
        Returns:
            Energía de acoplamiento
        """
        # Término dipolar
        H_dipole = self.mu * E
        
        # Término cuadrupolar
        H_quadrupole = self.Q * grad_E
        
        # Términos no lineales
        H_nonlinear = self.chi2 * E**2 + self.chi3 * E**3
        
        return H_dipole + H_quadrupole + H_nonlinear


# ==================== II. FORMALISMO ESPECTRAL ====================

def psi_input(t: np.ndarray, A0: float, m: float, omega_p: float, 
              omega_0: float = OMEGA_0_QCAL) -> np.ndarray:
    """
    Señal de entrada modulada.
    
    Ψ_input(t) = A₀[1 + m·sin(ωₚt)]·sin(ω₀t)
    
    Args:
        t: Array de tiempos
        A0: Amplitud constante
        m: Índice de modulación (0-1)
        omega_p: Frecuencia de modulación (Hz)
        omega_0: Frecuencia portadora QCAL (Hz)
        
    Returns:
        Señal de entrada
    """
    omega_p_rad = 2 * np.pi * omega_p
    omega_0_rad = 2 * np.pi * omega_0
    
    envelope = A0 * (1 + m * np.sin(omega_p_rad * t))
    carrier = np.sin(omega_0_rad * t)
    
    return envelope * carrier


def energia_total(psi: np.ndarray, dt: float) -> float:
    """
    Calcula la energía total de la señal.
    
    E_total = ∫|Ψ_input(t)|²dt
    
    Args:
        psi: Señal de entrada
        dt: Paso de tiempo
        
    Returns:
        Energía total
    """
    # Use trapezoid (new) or trapz (old) for compatibility
    try:
        return np.trapezoid(psi**2, dx=dt)
    except AttributeError:
        return np.trapz(psi**2, dx=dt)


def normalize_energy(psi: np.ndarray, target_energy: float, dt: float) -> np.ndarray:
    """
    Normaliza la señal para mantener energía constante.
    
    Args:
        psi: Señal de entrada
        target_energy: Energía objetivo
        dt: Paso de tiempo
        
    Returns:
        Señal normalizada
    """
    current_energy = energia_total(psi, dt)
    scale_factor = np.sqrt(target_energy / current_energy)
    return psi * scale_factor


def respuesta_fluorescente(t: np.ndarray, F0: float, delta_F: float, 
                          eta: float, omega_p: float, phi: float) -> np.ndarray:
    """
    Ecuación de respuesta fluorescente.
    
    F(t) = F₀ + ΔF(ωₚ)·[1 + η·sin(ωₚt + φ(ωₚ))]
    
    Args:
        t: Array de tiempos
        F0: Fluorescencia basal
        delta_F: Amplitud de respuesta
        eta: Eficiencia de transferencia
        omega_p: Frecuencia de modulación
        phi: Desfase
        
    Returns:
        Respuesta fluorescente
    """
    omega_p_rad = 2 * np.pi * omega_p
    return F0 + delta_F * (1 + eta * np.sin(omega_p_rad * t + phi))


def parametro_qcal_critico(delta_F: float, dE_domega: float) -> float:
    """
    Parámetro crítico para falsar QCAL.
    
    η(ωₚ) = ΔF(ωₚ) / (∂E/∂ωₚ)
    
    Args:
        delta_F: Amplitud de respuesta
        dE_domega: Derivada de energía respecto a frecuencia
        
    Returns:
        Eficiencia η
    """
    if abs(dE_domega) < 1e-10:
        return 0.0
    return delta_F / dE_domega


# ==================== III. MODELO DINÁMICO DE RESONANCIA ====================

class CoupledProteinOscillator:
    """
    Modelo de oscilador acoplado para dominios proteicos.
    
    mᵢ d²xᵢ/dt² + γᵢ dxᵢ/dt + kᵢxᵢ + Σⱼ κᵢⱼ(xᵢ - xⱼ) = qᵢE(ωₚ,t)
    """
    
    def __init__(self, m: float, gamma: float, k: float, q: float):
        """
        Parámetros del oscilador.
        
        Args:
            m: Masa efectiva
            gamma: Coeficiente de amortiguamiento
            k: Constante elástica
            q: Carga efectiva
        """
        self.m = m
        self.gamma = gamma
        self.k = k
        self.q = q
        
        # Frecuencia de resonancia: ω_res = √(k/m)
        self.omega_res = np.sqrt(k / m)
    
    def susceptibilidad(self, omega: float) -> complex:
        """
        Susceptibilidad en espacio de Fourier.
        
        x̃ᵢ(ω) = [qᵢ/(mᵢ(ωᵢ² - ω²) + iγᵢω)]·Ẽ(ω)
        
        Args:
            omega: Frecuencia angular (rad/s)
            
        Returns:
            Susceptibilidad compleja
        """
        denominator = self.m * (self.omega_res**2 - omega**2) + 1j * self.gamma * omega
        return self.q / denominator
    
    def respuesta_frecuencia(self, omega: float, E_omega: complex) -> complex:
        """
        Respuesta en frecuencia.
        
        Args:
            omega: Frecuencia angular
            E_omega: Campo eléctrico en frecuencia
            
        Returns:
            Desplazamiento x̃(ω)
        """
        chi = self.susceptibilidad(omega)
        return chi * E_omega


def frecuencia_resonancia_qcal(k_eff: float, m_eff: float) -> float:
    """
    Calcula la frecuencia de resonancia QCAL.
    
    ω_res = √(k_eff/m_eff) ≈ 2π × 141.7 Hz
    
    Args:
        k_eff: Constante elástica efectiva
        m_eff: Masa efectiva
        
    Returns:
        Frecuencia de resonancia (Hz)
    """
    omega_res_rad = np.sqrt(k_eff / m_eff)
    return omega_res_rad / (2 * np.pi)


# ==================== IV. TRANSDUCCIÓN A FLUORESCENCIA ====================

def intensidad_fluorescencia_gfp(x: np.ndarray, x0: np.ndarray, 
                                 sigma: np.ndarray, alpha: np.ndarray) -> float:
    """
    Intensidad de fluorescencia para GFP.
    
    I_fluorescencia ∝ |〈S₁|μ|S₀〉|² × F(x₁, x₂, ..., x_N)
    F = exp[-Σᵢ (xᵢ - xᵢ⁰)²/2σᵢ²]
    
    Args:
        x: Coordenadas actuales
        x0: Coordenadas de equilibrio
        sigma: Desviaciones estándar
        alpha: Coeficientes de acoplamiento
        
    Returns:
        Intensidad relativa
    """
    # Aproximación armónica
    F = np.exp(-np.sum((x - x0)**2 / (2 * sigma**2)))
    
    # Suma ponderada
    I = np.sum(alpha * F)
    
    return I


def delta_I_sobre_I0(x_tilde: np.ndarray, alpha: np.ndarray, 
                     beta: np.ndarray = None) -> float:
    """
    Predicción matemática exacta del cambio de intensidad.
    
    ΔI/I₀ = Σᵢ αᵢ·|x̃ᵢ(ωₚ)|² + Σᵢⱼ βᵢⱼ·Re[x̃ᵢ(ωₚ)x̃ⱼ*(ωₚ)]
    
    Args:
        x_tilde: Desplazamientos en frecuencia (complejos)
        alpha: Coeficientes lineales
        beta: Matriz de coeficientes de acoplamiento
        
    Returns:
        Cambio relativo de intensidad
    """
    # Término lineal
    linear_term = np.sum(alpha * np.abs(x_tilde)**2)
    
    # Término de acoplamiento
    if beta is not None:
        N = len(x_tilde)
        coupling_term = 0.0
        for i in range(N):
            for j in range(N):
                coupling_term += beta[i, j] * np.real(x_tilde[i] * np.conj(x_tilde[j]))
    else:
        coupling_term = 0.0
    
    return linear_term + coupling_term


# ==================== V. PREDICCIONES CUANTITATIVAS QCAL ====================

def prediccion_resonancia(omega_p: float, omega_0: float = OMEGA_0_QCAL,
                         harmonics: List[Tuple[int, int]] = None) -> Dict[str, float]:
    """
    Predicción 1: Resonancia en ωₚ/ω₀ = p/q.
    
    Args:
        omega_p: Frecuencia de modulación
        omega_0: Frecuencia QCAL
        harmonics: Lista de tuplas (p, q) a verificar
        
    Returns:
        Diccionario con distancias a resonancias
    """
    if harmonics is None:
        # Armónicos de Magicicada
        harmonics = [(1, 1), (2, 1), (3, 1), (17, 13), (13, 17)]
    
    ratio = omega_p / omega_0
    
    resultados = {}
    for p, q in harmonics:
        target = p / q
        distance = abs(ratio - target)
        resultados[f"{p}/{q}"] = distance
    
    # Encuentra la resonancia más cercana
    min_key = min(resultados, key=resultados.get)
    resultados["closest"] = min_key
    resultados["min_distance"] = resultados[min_key]
    
    return resultados


def estructura_armonica_lorentziana(omega: np.ndarray, omega_0: float = OMEGA_0_QCAL,
                                    k_max: int = 5, A: np.ndarray = None,
                                    Gamma: np.ndarray = None) -> np.ndarray:
    """
    Predicción 2: Estructura armónica como suma de Lorentzianas.
    
    ΔF(ω) = Σₖ Aₖ / [(ω - kω₀)² + Γₖ²]
    
    Args:
        omega: Array de frecuencias
        omega_0: Frecuencia fundamental
        k_max: Número máximo de armónicos
        A: Amplitudes de cada armónico
        Gamma: Anchos de cada armónico
        
    Returns:
        Respuesta espectral
    """
    if A is None:
        A = np.ones(k_max) / np.arange(1, k_max + 1)  # Decreciente con k
    
    if Gamma is None:
        Gamma = 0.1 * omega_0 * np.ones(k_max)  # Ancho fijo
    
    delta_F = np.zeros_like(omega)
    
    for k in range(1, k_max + 1):
        omega_k = k * omega_0
        lorentzian = A[k-1] / ((omega - omega_k)**2 + Gamma[k-1]**2)
        delta_F += lorentzian
    
    return delta_F


def umbral_coherencia(psi: float, psi_critico: float = PSI_CRITICO) -> Dict[str, any]:
    """
    Predicción 3: Umbral de coherencia - punto de bifurcación.
    
    Ψ_crítico = 0.888 → ∂²ΔF/∂ω² cambia de signo
    
    Args:
        psi: Amplitud del campo
        psi_critico: Umbral crítico
        
    Returns:
        Estado del sistema respecto al umbral
    """
    ratio = psi / psi_critico
    
    return {
        "psi": psi,
        "psi_critico": psi_critico,
        "ratio": ratio,
        "above_threshold": psi > psi_critico,
        "bifurcation_regime": "coherent" if psi > psi_critico else "incoherent"
    }


# ==================== VI. PROTOCOLO EXPERIMENTAL ====================

class ExperimentalProtocol:
    """
    Protocolo matemático para barrido de frecuencia y medición.
    """
    
    def __init__(self, A0: float = 1.0, m: float = 0.5, 
                 omega_0: float = OMEGA_0_QCAL):
        """
        Args:
            A0: Amplitud base
            m: Índice de modulación
            omega_0: Frecuencia portadora
        """
        self.A0 = A0
        self.m = m
        self.omega_0 = omega_0
    
    def barrido_frecuencia(self, freq_range: np.ndarray, duration: float = 10.0,
                          sample_rate: float = 10000.0) -> Dict[float, Dict]:
        """
        Barrido de frecuencia manteniendo energía constante.
        
        Args:
            freq_range: Rango de frecuencias a barrer (Hz)
            duration: Duración de cada medición (s)
            sample_rate: Tasa de muestreo (Hz)
            
        Returns:
            Diccionario con resultados para cada frecuencia
        """
        t = np.linspace(0, duration, int(duration * sample_rate))
        dt = 1.0 / sample_rate
        
        resultados = {}
        
        # Calcular energía objetivo (primera frecuencia)
        psi_ref = psi_input(t, self.A0, self.m, freq_range[0], self.omega_0)
        E_target = energia_total(psi_ref, dt)
        
        for omega_p in freq_range:
            # Generar señal
            psi = psi_input(t, self.A0, self.m, omega_p, self.omega_0)
            
            # Normalizar energía
            psi_norm = normalize_energy(psi, E_target, dt)
            
            # Almacenar
            resultados[omega_p] = {
                "signal": psi_norm,
                "energy": energia_total(psi_norm, dt),
                "time": t
            }
        
        return resultados
    
    def medir_fluorescencia(self, signal: np.ndarray, t: np.ndarray,
                           F0: float = 100.0, response_func: Callable = None) -> Dict:
        """
        Medición de fluorescencia.
        
        Args:
            signal: Señal de estimulación
            t: Array de tiempos
            F0: Fluorescencia basal
            response_func: Función de respuesta del sistema
            
        Returns:
            Mediciones de fluorescencia
        """
        if response_func is None:
            # Respuesta por defecto (lineal con ruido)
            F = F0 * (1 + 0.01 * signal + 0.001 * np.random.randn(len(signal)))
        else:
            F = response_func(signal, t)
        
        # Promedio temporal
        F_mean = np.mean(F)
        
        # Correlación con señal
        correlation = np.correlate(F - F_mean, signal - np.mean(signal), mode='full')
        max_corr_idx = np.argmax(np.abs(correlation))
        
        # Fase (simplificado)
        phi = (max_corr_idx - len(signal)) * (2 * np.pi / len(signal))
        
        return {
            "fluorescence": F,
            "F_mean": F_mean,
            "F_std": np.std(F),
            "correlation": np.max(np.abs(correlation)),
            "phase": phi
        }
    
    def analisis_qcal(self, resultados_frecuencia: Dict[float, Dict],
                     sigma_threshold: float = 2.0) -> Dict:
        """
        Análisis QCAL: R(ω) = [F(ω) - F_promedio] / σ_F.
        
        Args:
            resultados_frecuencia: Resultados del barrido
            sigma_threshold: Umbral de significancia (σ)
            
        Returns:
            Análisis estadístico
        """
        frecuencias = list(resultados_frecuencia.keys())
        F_values = [resultados_frecuencia[f]["F_mean"] for f in frecuencias]
        
        F_mean = np.mean(F_values)
        F_std = np.std(F_values)
        
        # Calcular R(ω)
        R = {freq: (F - F_mean) / F_std if F_std > 0 else 0.0
             for freq, F in zip(frecuencias, F_values)}
        
        # Verificar resonancias QCAL
        resonancias_qcal = []
        for n in MAGICICADA_HARMONICS:
            freq_res = self.omega_0 / n
            # Buscar frecuencia más cercana
            closest_freq = min(frecuencias, key=lambda f: abs(f - freq_res))
            if abs(R[closest_freq]) > sigma_threshold:
                resonancias_qcal.append({
                    "harmonic": n,
                    "freq_teorica": freq_res,
                    "freq_medida": closest_freq,
                    "R_value": R[closest_freq],
                    "significativo": True
                })
        
        return {
            "R_values": R,
            "F_mean": F_mean,
            "F_std": F_std,
            "resonancias_detectadas": resonancias_qcal,
            "confirmacion_qcal": len(resonancias_qcal) > 0
        }


# ==================== VII. CONTROLES DE FALSACIÓN ====================

def hipotesis_nula_test(F_resonante: np.ndarray, F_no_resonante: np.ndarray,
                       alpha: float = 0.001) -> Dict:
    """
    Test estadístico exacto: ANOVA espectral.
    
    H₀: ΔF(ω) = constante ∀ ω (misma energía → misma respuesta)
    
    F_stat = [SS_between(ω)/df₁] / [SS_within(ω)/df₂]
    
    Args:
        F_resonante: Fluorescencia en frecuencias resonantes
        F_no_resonante: Fluorescencia en frecuencias no resonantes
        alpha: Nivel de significancia
        
    Returns:
        Resultados del test ANOVA
    """
    # Número de grupos
    k = 2
    
    # Tamaños
    n1 = len(F_resonante)
    n2 = len(F_no_resonante)
    N = n1 + n2
    
    # Medias
    mean_res = np.mean(F_resonante)
    mean_no_res = np.mean(F_no_resonante)
    mean_total = (n1 * mean_res + n2 * mean_no_res) / N
    
    # SS between
    SS_between = n1 * (mean_res - mean_total)**2 + n2 * (mean_no_res - mean_total)**2
    
    # SS within
    SS_within = np.sum((F_resonante - mean_res)**2) + np.sum((F_no_resonante - mean_no_res)**2)
    
    # Grados de libertad
    df1 = k - 1
    df2 = N - k
    
    # F-statistic
    if SS_within == 0:
        F_stat = np.inf
    else:
        F_stat = (SS_between / df1) / (SS_within / df2)
    
    # Valor crítico
    F_critical = f_distribution.ppf(1 - alpha, df1, df2)
    
    # p-value
    p_value = 1 - f_distribution.cdf(F_stat, df1, df2)
    
    return {
        "F_statistic": F_stat,
        "F_critical": F_critical,
        "p_value": p_value,
        "df1": df1,
        "df2": df2,
        "rechazar_H0": F_stat > F_critical,
        "significancia": alpha,
        "conclusion": "QCAL confirmado" if F_stat > F_critical else "QCAL no confirmado"
    }


# ==================== VIII. PROCESAMIENTO DE SEÑAL ====================

def filtro_gaussiano(F_raw: np.ndarray, t: np.ndarray, tau: float) -> np.ndarray:
    """
    Filtro Gaussiano para limpieza de señal.
    
    F_limpieza(t) = F_raw(t) * exp(-t²/2τ²)
    
    Args:
        F_raw: Señal cruda
        t: Tiempos
        tau: Constante de tiempo
        
    Returns:
        Señal filtrada
    """
    gaussian_window = np.exp(-t**2 / (2 * tau**2))
    return F_raw * gaussian_window


def analisis_espectral(F: np.ndarray, dt: float) -> Dict:
    """
    Análisis espectral con FFT.
    
    Args:
        F: Señal temporal
        dt: Paso de tiempo
        
    Returns:
        Análisis espectral
    """
    # FFT
    F_fft = fft.fft(F)
    freqs = fft.fftfreq(len(F), dt)
    
    # Solo frecuencias positivas
    positive_idx = freqs > 0
    freqs_pos = freqs[positive_idx]
    F_fft_pos = F_fft[positive_idx]
    
    power_spectrum = np.abs(F_fft_pos)**2
    
    return {
        "frequencies": freqs_pos,
        "fft": F_fft_pos,
        "power_spectrum": power_spectrum,
        "peak_freq": freqs_pos[np.argmax(power_spectrum)]
    }


def calcular_snr(F_spectral: np.ndarray, omega_p: float, 
                freqs: np.ndarray, bandwidth: float = 1.0) -> float:
    """
    Calcula SNR espectral.
    
    SNR = |F_espectral(ωₚ)| / rms[F_espectral(ω≠ωₚ)]
    
    Args:
        F_spectral: Espectro de potencia
        omega_p: Frecuencia de interés
        freqs: Array de frecuencias
        bandwidth: Ancho de banda alrededor de ωₚ (Hz)
        
    Returns:
        SNR
    """
    # Índice de frecuencia de interés
    idx_signal = np.argmin(np.abs(freqs - omega_p))
    
    # Máscara para ruido (excluyendo bandwidth alrededor de ωₚ)
    noise_mask = np.abs(freqs - omega_p) > bandwidth
    
    # Señal
    signal_power = F_spectral[idx_signal]
    
    # Ruido (RMS)
    noise_rms = np.sqrt(np.mean(F_spectral[noise_mask]**2))
    
    if noise_rms == 0:
        return np.inf
    
    return signal_power / noise_rms


def criterio_deteccion_positiva(snr: float, coherencia: float,
                                snr_threshold: float = 3.0,
                                coherencia_threshold: float = 0.7) -> Dict:
    """
    Criterio de detección positiva.
    
    SNR > 3 Y coherencia[F(t), Ψ(t)] > 0.7
    
    Args:
        snr: Signal-to-noise ratio
        coherencia: Coherencia entre F y Ψ
        snr_threshold: Umbral de SNR
        coherencia_threshold: Umbral de coherencia
        
    Returns:
        Resultado de detección
    """
    deteccion_positiva = (snr > snr_threshold) and (coherencia > coherencia_threshold)
    
    return {
        "snr": snr,
        "coherencia": coherencia,
        "snr_threshold": snr_threshold,
        "coherencia_threshold": coherencia_threshold,
        "snr_ok": snr > snr_threshold,
        "coherencia_ok": coherencia > coherencia_threshold,
        "deteccion_positiva": deteccion_positiva
    }


# ==================== IX. ECUACIÓN DE ESTADO QCAL ====================

def ecuacion_estado_qcal(F: np.ndarray, psi: np.ndarray, t: np.ndarray,
                        D: float = 1.0, gamma: float = 0.1, 
                        kappa: float = 10.0) -> np.ndarray:
    """
    Ecuación de estado QCAL confirmada.
    
    ∂F/∂t = D·∇²F - γF + κ·|Ψ(ω_res,t)|²
    
    con κ >> γ (acoplamiento fuerte)
    
    Args:
        F: Fluorescencia
        psi: Campo QCAL
        t: Tiempo
        D: Coeficiente de difusión
        gamma: Tasa de decaimiento
        kappa: Coeficiente de acoplamiento
        
    Returns:
        dF/dt
    """
    # Término de difusión (aproximación 1D)
    laplacian_F = np.gradient(np.gradient(F))
    
    # Término de decaimiento
    decay = -gamma * F
    
    # Término de acoplamiento
    coupling = kappa * np.abs(psi)**2
    
    return D * laplacian_F + decay + coupling


# ==================== X. UTILIDADES ====================

def generar_reporte_experimento(parametros: Dict, resultados: Dict) -> str:
    """
    Genera reporte del experimento QCAL.
    
    Args:
        parametros: Parámetros experimentales
        resultados: Resultados obtenidos
        
    Returns:
        Reporte formateado
    """
    report = []
    report.append("=" * 70)
    report.append("REPORTE EXPERIMENTAL - ACOPLAMIENTO VIBRO-FLUORESCENTE QCAL")
    report.append("=" * 70)
    report.append("")
    
    report.append("PARÁMETROS:")
    for key, value in parametros.items():
        report.append(f"  {key}: {value}")
    report.append("")
    
    report.append("RESULTADOS:")
    for key, value in resultados.items():
        report.append(f"  {key}: {value}")
    report.append("")
    
    report.append("=" * 70)
    report.append("Frequency: 141.7001 Hz ∞³")
    report.append("=" * 70)
    
    return "\n".join(report)


if __name__ == "__main__":
    print("=" * 70)
    print("QCAL ∞³ - Vibro-Fluorescence Coupling Framework")
    print("=" * 70)
    print()
    print(f"Frecuencia QCAL: {OMEGA_0_QCAL} Hz")
    print(f"Umbral crítico Ψ: {PSI_CRITICO}")
    print(f"Constante κ_Π: {KAPPA_PI}")
    print()
    print("Framework listo para experimentos de falsación QCAL.")
    print()
    print("=" * 70)
