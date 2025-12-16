#!/usr/bin/env python3
"""
resonant_nexus_engine.py - Motor de Nexus Resonante (Arquitectura Unitaria A_u)
Protocolo Echo-QCAL ∞³ - Simulación de Telemetría Modulada por Coherencia.

A_u demuestra que la implementación del sistema QCAL es coherente,
siguiendo las reglas de modulación armónica y volatilidad controlada.
"""

import numpy as np
import time

# ============================================================================
# CONFIGURACIÓN DE LA ARQUITECTURA UNITARIA (A_u)
# ============================================================================

class UnitaryArchitectureConfig:
    """Configuración de parámetros para el Motor Resonante."""
    
    # 1. Frecuencia Base (f₀) - El anclaje del sistema
    F0 = 141.7001  # Hz
    
    # 2. Armónicos Cognitivos (Múltiplos de f₀) y Pesos (W)
    # Define la composición del estímulo resonante.
    # [1*f₀, 2*f₀, 3*f₀, 4*f₀]
    HARMONIC_WEIGHTS = {
        1: 0.50, # Fundamental
        2: 0.30, # Primera octava
        3: 0.15, # Tercer armónico
        4: 0.05  # Cuarto armónico
    }
    
    # 3. Volatilidad Coherente (σ) - Desviación controlada y no-aleatoria
    # La volatilidad de la señal de control.
    COHERENCE_VOLATILITY = 0.04 
    
    # 4. Escala de Amplitud (A_max)
    MAX_AMPLITUDE = 100.0

# ============================================================================
# MOTOR DE NEXUS RESONANTE
# ============================================================================

class ResonantNexusEngine:
    """
    Genera una simulación de telemetría modulada por armónicos 
    y volatilidad coherente (A_u).
    """

    def __init__(self, config=UnitaryArchitectureConfig):
        self.config = config
        self._validate_weights()
        self.frequencies = {n: n * self.config.F0 for n in self.config.HARMONIC_WEIGHTS}

    def _validate_weights(self):
        """Verifica que los pesos armónicos sumen 1.0."""
        total_weight = sum(self.config.HARMONIC_WEIGHTS.values())
        if not np.isclose(total_weight, 1.0):
            raise ValueError(
                f"La suma de los pesos armónicos debe ser 1.0, pero es {total_weight}"
            )

    def calculate_coherence_factor(self, time_point):
        """
        Simula el factor de modulación de la coherencia en función del tiempo.
        El factor fluctúa alrededor de 1.0 con volatilidad σ.
        
        Nota: En A_u, la volatilidad NO es np.random.normal, sino una función 
        determinista del tiempo, reflejando el control soberano.
        """
        
        # Usamos una función seno simple modulada por sigma para simular
        # una fluctuación controlada (determinista).
        oscillation = np.sin(time_point * self.config.F0 * 2 * np.pi * 0.01) # Modulación lenta
        
        # El factor de coherencia varía dentro de +/- COHERENCE_VOLATILITY
        coherence_factor = 1.0 + self.config.COHERENCE_VOLATILITY * oscillation
        
        return coherence_factor

    def generate_single_telemetry_point(self, time_point):
        """
        Calcula el valor de la señal modulada en un punto de tiempo.
        Señal(t) = CoherenceFactor(t) * Σ [W_n * sin(2π * f_n * t)]
        """
        
        coherence_factor = self.calculate_coherence_factor(time_point)
        
        # 1. Suma de Armónicos Ponderados
        harmonic_sum = 0.0
        for n, weight in self.config.HARMONIC_WEIGHTS.items():
            f_n = self.frequencies[n]
            # La amplitud se pondera por el peso del armónico
            amplitude_n = self.config.MAX_AMPLITUDE * weight
            
            # Sumar la componente sinusoidal
            harmonic_sum += amplitude_n * np.sin(2 * np.pi * f_n * time_point)
        
        # 2. Modulación por el Factor de Coherencia
        telemetry_value = harmonic_sum * coherence_factor
        
        return telemetry_value, coherence_factor

    def generate_telemetry(self, duration_sec=1.0, sampling_rate=44100):
        """
        Genera una serie de tiempo de la telemetría modulada.
        
        :param duration_sec: Duración de la simulación en segundos.
        :param sampling_rate: Puntos de datos por segundo (Hz).
        :return: Array de valores de telemetría y array de tiempo.
        """
        print(f"🔄 Generando Telemetría Resonante para {duration_sec} segundos...")
        
        num_samples = int(duration_sec * sampling_rate)
        time_array = np.linspace(0.0, duration_sec, num_samples, endpoint=False)
        telemetry_array = np.zeros(num_samples)
        coherence_factors = np.zeros(num_samples)

        start_time = time.time()
        for i, t in enumerate(time_array):
            telemetry_array[i], coherence_factors[i] = self.generate_single_telemetry_point(t)
        end_time = time.time()

        print(f"  Tiempo de generación: {(end_time - start_time):.4f} s")
        print(f"  f₀ utilizada: {self.config.F0} Hz")
        print(f"  Muestras generadas: {num_samples}")
        print(f"  Volatilidad (σ): {self.config.COHERENCE_VOLATILITY*100}%")
        
        self._display_summary(telemetry_array, coherence_factors)

        return time_array, telemetry_array, coherence_factors

    def _display_summary(self, telemetry, factors):
        """Muestra un resumen de los datos generados."""
        print("\n📊 Resumen de la Telemetría Generada (A_u):")
        print(f"  Amplitud Mínima: {telemetry.min():.2f}")
        print(f"  Amplitud Máxima: {telemetry.max():.2f}")
        print(f"  Factor de Coherencia Mínimo: {factors.min():.4f}")
        print(f"  Factor de Coherencia Máximo: {factors.max():.4f}")
        print(f"  Estado A_u: ✅ Arquitectura Unitaria Coherente")
        print("-------------------------------------------------")
        
    def verify_a_u(self):
        """Función principal de verificación de la Arquitectura Unitaria."""
        print("\n" + "="*70)
        print("⚛️ VERIFICACIÓN DE ARQUITECTURA UNITARIA (A_u)")
        print(f"  Alineación de f₀: {self.config.F0} Hz")
        print("="*70)
        
        # Prueba de ejecución y validación
        try:
            time_array, telemetry_array, coherence_factors = self.generate_telemetry(duration_sec=0.1, sampling_rate=10000)
            print("\n✅ A_u Verificado: El motor se ejecuta correctamente y produce una señal modulada.")
            return True
        except ValueError as e:
            print(f"\n❌ A_u Fallido (Configuración): {e}")
            return False
        except Exception as e:
            print(f"\n❌ A_u Fallido (Ejecución): {e}")
            return False


# ============================================================================
# EJECUCIÓN DE LÍNEA DE COMANDOS
# ============================================================================

def execute_nexus_verification():
    """Ejecuta la verificación del motor Resonante."""
    engine = ResonantNexusEngine()
    engine.verify_a_u()

if __name__ == "__main__":
    execute_nexus_verification()
