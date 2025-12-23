#!/usr/bin/env python3
"""
resonant_nexus_engine.py - Motor de Coherencia QCAL ∞³
Genera telemetría modulada por f₀ = 141.7001 Hz y armónicos cognitivos
"""

import numpy as np
from datetime import datetime
from typing import Dict, List, Optional
import json

# ============================================================================
# CONSTANTES QCAL
# ============================================================================

class ConstantesQCAL:
    """Constantes del marco QCAL ∞³"""
    
    # Frecuencia base de coherencia universal
    F0 = 141.7001  # Hz
    
    # Período fundamental
    TAU0 = 1.0 / F0  # 0.00705715 segundos
    
    # Armónicos cognitivos
    ARMONICOS = [1, 2, 3, 4]  # Múltiplos de f₀
    PESOS_ARMONICOS = [0.50, 0.30, 0.15, 0.05]  # Distribución de energía
    
    # Volatilidad coherente (no aleatoria)
    SIGMA_COHERENTE = 0.04
    
    # Metadata
    PROTOCOL = "Echo-QCAL ∞³"
    VERSION = "1.0.0"

# ============================================================================
# MOTOR DE RESONANCIA
# ============================================================================

class ResonantNexusEngine:
    """Motor principal de generación de telemetría coherente"""
    
    def __init__(self, seed: Optional[int] = None):
        """
        Inicializa el motor de resonancia
        
        Args:
            seed: Semilla para reproducibilidad (opcional)
        """
        self.constantes = ConstantesQCAL()
        if seed is not None:
            np.random.seed(seed)
        
        self.metadata = {
            "protocol": self.constantes.PROTOCOL,
            "version": self.constantes.VERSION,
            "f0": self.constantes.F0,
            "tau0": self.constantes.TAU0,
            "timestamp_init": datetime.utcnow().isoformat() + "Z"
        }
    
    def generate_telemetry(self, cycles: int = 1000, t_start: float = 0.0) -> Dict:
        """
        Genera telemetría modulada por f₀ y armónicos
        
        Args:
            cycles: Número de ciclos a generar
            t_start: Tiempo inicial (segundos)
        
        Returns:
            Diccionario con telemetría generada
        """
        # Generar timestamps
        dt = self.constantes.TAU0
        t = np.arange(t_start, t_start + cycles * dt, dt)
        
        # Generar señal base modulada por armónicos
        signal = np.zeros_like(t)
        
        for harmonico, peso in zip(self.constantes.ARMONICOS, self.constantes.PESOS_ARMONICOS):
            freq = harmonico * self.constantes.F0
            phase = np.random.uniform(0, 2 * np.pi)  # Fase aleatoria para cada armónico
            signal += peso * np.sin(2 * np.pi * freq * t + phase)
        
        # Agregar volatilidad coherente
        coherent_noise = self.constantes.SIGMA_COHERENTE * np.random.randn(len(t))
        signal += coherent_noise
        
        # Normalizar
        signal = (signal - signal.mean()) / signal.std()
        
        # Construir resultado
        telemetry = {
            "metadata": self.metadata,
            "parameters": {
                "cycles": cycles,
                "t_start": t_start,
                "dt": dt,
                "n_samples": len(t)
            },
            "data": {
                "time": t.tolist(),
                "signal": signal.tolist(),
                "harmonics_used": self.constantes.ARMONICOS,
                "weights": self.constantes.PESOS_ARMONICOS
            },
            "statistics": {
                "mean": float(signal.mean()),
                "std": float(signal.std()),
                "min": float(signal.min()),
                "max": float(signal.max())
            }
        }
        
        return telemetry
    
    def verify_coherence(self, signal: np.ndarray, tolerance: float = 0.1) -> Dict:
        """
        Verifica que la señal mantiene coherencia con f₀
        
        Args:
            signal: Señal a verificar
            tolerance: Tolerancia para verificación (default: 10%)
        
        Returns:
            Resultados de verificación
        """
        # FFT para análisis de frecuencias
        fft = np.fft.fft(signal)
        freqs = np.fft.fftfreq(len(signal), self.constantes.TAU0)
        
        # Encontrar picos principales
        power = np.abs(fft) ** 2
        positive_freqs = freqs > 0
        
        # Buscar f₀ y armónicos
        detected_harmonics = []
        for harmonico in self.constantes.ARMONICOS:
            target_freq = harmonico * self.constantes.F0
            
            # Buscar en ventana de tolerancia
            mask = (freqs >= target_freq * (1 - tolerance)) & (freqs <= target_freq * (1 + tolerance))
            if np.any(mask):
                idx = np.argmax(power[mask])
                detected_freq = freqs[mask][idx]
                detected_harmonics.append({
                    "harmonic": harmonico,
                    "expected": target_freq,
                    "detected": float(detected_freq),
                    "error": float(abs(detected_freq - target_freq) / target_freq)
                })
        
        coherence_score = len(detected_harmonics) / len(self.constantes.ARMONICOS)
        
        return {
            "coherent": coherence_score > 0.75,
            "coherence_score": coherence_score,
            "detected_harmonics": detected_harmonics,
            "tolerance": tolerance
        }
    
    def export_telemetry(self, telemetry: Dict, filename: str):
        """Exporta telemetría a archivo JSON"""
        with open(filename, 'w') as f:
            json.dump(telemetry, f, indent=2)
        print(f"📊 Telemetría exportada a: {filename}")

# ============================================================================
# FUNCIONES DE UTILIDAD
# ============================================================================

def quick_generate(cycles: int = 1000) -> Dict:
    """Genera telemetría rápidamente"""
    engine = ResonantNexusEngine()
    return engine.generate_telemetry(cycles=cycles)

def verify_signal(signal: np.ndarray) -> bool:
    """Verificación rápida de coherencia"""
    engine = ResonantNexusEngine()
    result = engine.verify_coherence(signal)
    return result["coherent"]

# ============================================================================
# DEMO Y TEST
# ============================================================================

if __name__ == "__main__":
    print("🔄 Resonant Nexus Engine - Demo")
    print("="*70)
    
    # Crear motor
    engine = ResonantNexusEngine(seed=42)
    
    # Generar telemetría
    print("\n📊 Generando telemetría con f₀ = 141.7001 Hz...")
    telemetry = engine.generate_telemetry(cycles=1000)
    
    print(f"   Muestras generadas: {telemetry['parameters']['n_samples']}")
    print(f"   Período: {telemetry['metadata']['tau0']:.8f} s")
    print(f"   Armónicos: {telemetry['data']['harmonics_used']}")
    print(f"   Pesos: {telemetry['data']['weights']}")
    
    # Verificar coherencia
    print("\n🔍 Verificando coherencia...")
    signal = np.array(telemetry['data']['signal'])
    coherence = engine.verify_coherence(signal)
    
    print(f"   Coherencia: {'✅ SÍ' if coherence['coherent'] else '❌ NO'}")
    print(f"   Score: {coherence['coherence_score']:.2%}")
    print(f"   Armónicos detectados: {len(coherence['detected_harmonics'])}/{len(engine.constantes.ARMONICOS)}")
    
    for h in coherence['detected_harmonics']:
        print(f"      {h['harmonic']}f₀: {h['detected']:.2f} Hz (esperado: {h['expected']:.2f} Hz, error: {h['error']:.2%})")
    
    # Estadísticas
    print("\n📈 Estadísticas:")
    stats = telemetry['statistics']
    for key, value in stats.items():
        print(f"   {key}: {value:.4f}")
    
    print("\n✨ Demo completada exitosamente")
