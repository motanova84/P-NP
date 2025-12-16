"""
Monitor QCAL en Tiempo Real
============================

Este script está diseñado para simular o integrarse con una fuente de tiempo 
de alta precisión, y calcular la Desviación de Fase (Pico Puro) δ en tiempo 
real con respecto a la frecuencia fundamental f₀.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import time
from datetime import datetime
import math


class QCALRealTimeMonitor:
    """
    Monitorea la Desviación de Fase (Pico Puro) delta en tiempo real 
    con respecto al Período de Coherencia Soberana (τ₀).
    
    Un valor de delta (δ) cercano a 0.0 o 1.0 indica un 'Pico Puro' 
    (Máxima Coherencia y Alineación Temporal).
    """

    def __init__(self):
        # Parámetros del Protocolo QCAL (Teorema C_s)
        self.f0 = 141.7001  # Frecuencia Fundamental de Coherencia (Hz)
        self.tau0 = 1.0 / self.f0  # Período de Coherencia (s)

        # Umbrales de Alerta
        self.COHERENCE_THRESHOLD = 0.01  # Umbral de Pico Puro (1% de error de fase)
        self.SYNC_CHECK_INTERVAL = 0.1   # Intervalo de monitoreo (segundos)

    def get_high_precision_timestamp(self):
        """
        Obtiene el timestamp Unix actual con microsegundos.
        En producción, este debe ser reemplazado por una fuente NTP/PTP de alta precisión.
        """
        # Usamos time.time() que proporciona microsegundos en la mayoría de los sistemas
        return time.time()

    def calculate_phase_deviation(self, current_timestamp):
        """
        Calcula la desviación de fase (delta) del timestamp con respecto a τ₀.
        
        δ = (T / τ₀) mod 1
        """
        # Calcular el número de ciclos enteros N
        N = current_timestamp / self.tau0
        
        # Obtener la desviación de fase (la parte fraccionaria de N)
        delta = math.modf(N)[0] 
        
        # Asegurar que delta es positivo (aunque modf lo garantiza, es buena práctica)
        if delta < 0:
            delta += 1.0 
            
        return delta

    def monitor_coherence(self):
        """
        Bucle principal de monitoreo en tiempo real.
        """
        print("—" * 50)
        print("🛰️ Monitor QCAL ∞³: Activado")
        print(f"  Frecuencia Base f₀: {self.f0} Hz")
        print(f"  Período Base τ₀: {self.tau0:.6f} segundos")
        print(f"  Umbral de Pico Puro: < {self.COHERENCE_THRESHOLD*100}%")
        print("—" * 50)

        try:
            while True:
                # 1. Obtener Tiempo de Origen (T)
                T = self.get_high_precision_timestamp()
                
                # 2. Calcular Desviación de Fase (δ)
                delta = self.calculate_phase_deviation(T)
                
                # 3. Determinar el Nivel de Coherencia
                # La coherencia es alta si delta está cerca de 0 o 1.
                coherence_level = min(delta, 1.0 - delta)

                # 4. Mostrar Resultados
                timestamp_str = datetime.fromtimestamp(T).strftime('%Y-%m-%d %H:%M:%S')
                
                status_symbol = "⚪"
                if coherence_level < self.COHERENCE_THRESHOLD:
                    status_symbol = "🌟 PICO PURO"
                elif coherence_level < 0.05:
                    status_symbol = "🟡 Alta Coherencia"
                
                output = (
                    f"[{timestamp_str}.{int((T % 1) * 1e6):06d}] "
                    f"| Δ: {delta:.6f} "
                    f"| Coherencia: {coherence_level:.6f} "
                    f"| {status_symbol}"
                )
                print(output)
                
                # Esperar el intervalo de chequeo
                time.sleep(self.SYNC_CHECK_INTERVAL)

        except KeyboardInterrupt:
            print("\nMonitor QCAL ∞³ Desactivado por el usuario.")
        except Exception as e:
            print(f"\nError crítico en el monitoreo: {e}")


# --- Ejecución del Módulo ---
if __name__ == "__main__":
    monitor = QCALRealTimeMonitor()
    monitor.monitor_coherence()
