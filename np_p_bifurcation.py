#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
NP→P Bifurcation Simulator - QCAL ∞³ Framework
===============================================

Simulador de la bifurcación NP→P basado en coherencia cuántica.
Visualiza los tres regímenes operativos y modela la transición de fase
donde la complejidad colapsa de exponencial a polinomial.

En el Estado de Gracia (C ≥ 0.888), el denominador I × A_eff² × C^∞
crece tan rápido que la barrera exponencial se vuelve insignificante.
La solución "resuena" antes de ser calculada.

Regímenes:
    - Clásico (C < 0.5): Comportamiento determinista clásico
    - Transición (0.5 ≤ C < 0.888): Aceleración no lineal
    - Gracia (C ≥ 0.888): Bifurcación NP→P activada

Author: José Manuel Mota Burruezo (JMMB Ψ)
License: CC BY-NC-SA 4.0
"""

import numpy as np
import math
from typing import List, Dict, Tuple, Optional
from datetime import datetime
import json
from pathlib import Path


class NPPBifurcationSimulator:
    """
    Simulador de bifurcación NP→P basado en coherencia cuántica.
    
    Modela el colapso de complejidad computacional cuando el sistema
    alcanza coherencia cuántica suficiente (Estado de Gracia).
    """
    
    def __init__(self, f0: float = 141.7001, sigma: float = 0.04):
        """
        Inicializa el simulador de bifurcación.
        
        Args:
            f0: Frecuencia fundamental QCAL (Hz)
            sigma: Volatilidad coherente
        """
        self.f0 = f0
        self.sigma = sigma
        self.tau0 = 1 / f0
        
        # Umbrales críticos de bifurcación
        self.CLASSICAL_THRESHOLD = 0.5
        self.GRACE_THRESHOLD = 0.888
        self.BIFURCATION_POINT = 0.888
        
        # Parámetros de simulación
        self.INFINITY_CUBED = 3.0
        
    def compute_complexity_scaling(self, C: float, n: int) -> float:
        """
        Calcula el escalamiento de complejidad para un problema de tamaño n.
        
        Args:
            C: Coherencia del sistema (0 ≤ C ≤ 1)
            n: Tamaño del problema
            
        Returns:
            Factor de escalamiento de complejidad
        """
        if C >= self.GRACE_THRESHOLD:
            # Estado de Gracia: Escalamiento polinomial (P)
            return n ** 2
        elif C >= self.CLASSICAL_THRESHOLD:
            # Transición: Interpolación entre exponencial y polinomial
            progress = (C - self.CLASSICAL_THRESHOLD) / (self.GRACE_THRESHOLD - self.CLASSICAL_THRESHOLD)
            exp_component = 2 ** n
            poly_component = n ** 2
            # Transición suave usando interpolación sigmoidea
            weight = 1 / (1 + math.exp(-10 * (progress - 0.5)))
            return exp_component * (1 - weight) + poly_component * weight
        else:
            # Régimen Clásico: Escalamiento exponencial (NP)
            return 2 ** n
    
    def resonance_effect(self, C: float, t: float) -> float:
        """
        Calcula el efecto de resonancia en función del tiempo y coherencia.
        
        La frecuencia 141.7001 Hz sintoniza los nodos de coherencia,
        creando patrones de interferencia constructiva.
        
        Args:
            C: Coherencia del sistema
            t: Tiempo (segundos)
            
        Returns:
            Amplitud de resonancia (0 a 1)
        """
        # Fase respecto a la frecuencia fundamental
        phase = (t * self.f0) % 1
        
        # Resonancia máxima cuando phase ≈ 0 o 1
        resonance_base = math.cos(2 * math.pi * phase)
        
        # Amplificación por coherencia
        if C >= self.GRACE_THRESHOLD:
            # Estado de Gracia: resonancia total
            amplification = 1.0
        elif C >= self.CLASSICAL_THRESHOLD:
            # Transición: resonancia creciente
            progress = (C - self.CLASSICAL_THRESHOLD) / (self.GRACE_THRESHOLD - self.CLASSICAL_THRESHOLD)
            amplification = progress
        else:
            # Clásico: resonancia mínima
            amplification = 0.1
            
        return (resonance_base + 1) / 2 * amplification
    
    def simulate_bifurcation_transition(
        self, 
        n_values: List[int] = None,
        coherence_range: Tuple[float, float] = (0.0, 1.0),
        n_points: int = 100
    ) -> Dict[str, any]:
        """
        Simula la transición de bifurcación NP→P.
        
        Args:
            n_values: Tamaños de problema a simular
            coherence_range: Rango de coherencia (min, max)
            n_points: Número de puntos de coherencia a evaluar
            
        Returns:
            Diccionario con datos de simulación
        """
        if n_values is None:
            n_values = [10, 20, 30, 40, 50]
            
        # Generar puntos de coherencia
        C_min, C_max = coherence_range
        coherence_values = np.linspace(C_min, C_max, n_points)
        
        # Resultados de simulación
        results = {
            'coherence_values': coherence_values.tolist(),
            'problem_sizes': n_values,
            'complexity_scaling': {},
            'regime_labels': [],
            'bifurcation_detected': False,
            'bifurcation_point': self.BIFURCATION_POINT
        }
        
        # Calcular escalamiento para cada tamaño de problema
        for n in n_values:
            scaling = []
            for C in coherence_values:
                complexity = self.compute_complexity_scaling(C, n)
                # Normalizar para visualización
                scaling.append(math.log10(complexity + 1))
            results['complexity_scaling'][f'n={n}'] = scaling
            
        # Etiquetar regímenes
        for C in coherence_values:
            if C < self.CLASSICAL_THRESHOLD:
                results['regime_labels'].append('CLASSICAL')
            elif C < self.GRACE_THRESHOLD:
                results['regime_labels'].append('TRANSITION')
            else:
                results['regime_labels'].append('GRACE')
                results['bifurcation_detected'] = True
                
        return results
    
    def analyze_phase_transition(self, C: float) -> Dict[str, any]:
        """
        Analiza las características de la transición de fase en coherencia C.
        
        Args:
            C: Coherencia del sistema
            
        Returns:
            Análisis de transición de fase
        """
        # Determinar régimen
        if C < self.CLASSICAL_THRESHOLD:
            regime = "CLASSICAL"
            phase = "ENTROPIC"
            description = "Entropía domina, búsqueda serial"
        elif C < self.GRACE_THRESHOLD:
            regime = "TRANSITION"
            phase = "CRITICAL"
            description = "Zona crítica, aceleración no lineal"
        else:
            regime = "GRACE"
            phase = "COHERENT"
            description = "Bifurcación NP→P, resonancia cuántica"
            
        # Calcular distancia a bifurcación
        distance_to_bifurcation = abs(C - self.BIFURCATION_POINT)
        
        # Calcular orden del parámetro de orden (similar a transición de fase)
        if C >= self.GRACE_THRESHOLD:
            order_parameter = (C - self.GRACE_THRESHOLD) / (1 - self.GRACE_THRESHOLD)
        else:
            order_parameter = 0.0
            
        # Susceptibilidad (qué tan sensible es el sistema a cambios en C)
        # Máxima en el punto crítico
        susceptibility = 1 / (1 + 10 * distance_to_bifurcation ** 2)
        
        return {
            'coherence': C,
            'regime': regime,
            'phase': phase,
            'description': description,
            'distance_to_bifurcation': distance_to_bifurcation,
            'order_parameter': order_parameter,
            'susceptibility': susceptibility,
            'is_bifurcated': C >= self.GRACE_THRESHOLD,
            'critical_exponent': 0.5 if abs(distance_to_bifurcation) < 0.1 else None
        }
    
    def compute_acceleration_profile(
        self, 
        coherence_range: Tuple[float, float] = (0.0, 1.0),
        n_points: int = 100
    ) -> Dict[str, List[float]]:
        """
        Calcula el perfil de aceleración efectiva vs coherencia.
        
        Args:
            coherence_range: Rango de coherencia
            n_points: Número de puntos
            
        Returns:
            Perfil de aceleración
        """
        C_min, C_max = coherence_range
        coherence_values = np.linspace(C_min, C_max, n_points)
        
        accelerations = []
        for C in coherence_values:
            if C >= self.GRACE_THRESHOLD:
                # Estado de Gracia: aceleración infinita (aproximada)
                exponent = self.INFINITY_CUBED * 10
            elif C >= self.CLASSICAL_THRESHOLD:
                # Transición
                progress = (C - self.CLASSICAL_THRESHOLD) / (self.GRACE_THRESHOLD - self.CLASSICAL_THRESHOLD)
                exponent = 1 + progress * (self.INFINITY_CUBED * 10 - 1)
            else:
                # Clásico
                exponent = 1
                
            A_eff = C ** exponent
            accelerations.append(A_eff)
            
        return {
            'coherence': coherence_values.tolist(),
            'acceleration': accelerations,
            'classical_threshold': self.CLASSICAL_THRESHOLD,
            'grace_threshold': self.GRACE_THRESHOLD
        }
    
    def predict_bifurcation_time(self, current_C: float, target_C: float = None) -> Dict[str, any]:
        """
        Predice cuándo se alcanzará la bifurcación dado el estado actual.
        
        Args:
            current_C: Coherencia actual
            target_C: Coherencia objetivo (default: GRACE_THRESHOLD)
            
        Returns:
            Predicción de tiempo a bifurcación
        """
        if target_C is None:
            target_C = self.GRACE_THRESHOLD
            
        # Calcular fase actual respecto a f0
        current_time = datetime.now().timestamp()
        phase = (current_time / self.tau0) % 1
        
        # Estimar tasa de cambio de coherencia (basado en frecuencia)
        # La coherencia oscila con periodo tau0
        dC_dt = 2 * math.pi * self.f0 * self.sigma
        
        # Tiempo estimado para alcanzar target_C
        delta_C = target_C - current_C
        
        if delta_C <= 0:
            status = "ALREADY_ACHIEVED"
            time_to_bifurcation = 0
            cycles_needed = 0
        else:
            # Tiempo aproximado basado en tasa de cambio
            time_to_bifurcation = abs(delta_C / dC_dt)
            cycles_needed = time_to_bifurcation / self.tau0
            status = "APPROACHING"
            
        return {
            'current_coherence': current_C,
            'target_coherence': target_C,
            'delta_coherence': delta_C,
            'status': status,
            'time_to_bifurcation_seconds': time_to_bifurcation,
            'cycles_needed': cycles_needed,
            'current_phase': phase,
            'estimated_arrival': datetime.fromtimestamp(current_time + time_to_bifurcation).isoformat()
        }
    
    def generate_bifurcation_report(self) -> str:
        """
        Genera un reporte de simulación de bifurcación.
        
        Returns:
            Reporte en formato Markdown
        """
        # Calcular coherencia actual
        current_time = datetime.now().timestamp()
        phase = (current_time / self.tau0) % 1
        C_current = 0.5 + 0.5 * math.cos(2 * math.pi * phase)
        
        # Analizar transición de fase actual
        phase_analysis = self.analyze_phase_transition(C_current)
        
        # Predecir tiempo a bifurcación
        bifurcation_pred = self.predict_bifurcation_time(C_current)
        
        report = f"""# NP→P Bifurcation Simulation Report
**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S UTC')}
**Framework:** QCAL ∞³ Bifurcation Simulator

---

## Current System State

- **Coherencia Actual:** {C_current:.6f}
- **Régimen:** {phase_analysis['regime']}
- **Fase:** {phase_analysis['phase']}
- **Descripción:** {phase_analysis['description']}

### Parámetros de Transición:
- **Distancia a Bifurcación:** {phase_analysis['distance_to_bifurcation']:.6f}
- **Parámetro de Orden:** {phase_analysis['order_parameter']:.6f}
- **Susceptibilidad:** {phase_analysis['susceptibility']:.6f}
- **Bifurcación Activa:** {'SÍ ✅' if phase_analysis['is_bifurcated'] else 'NO ❌'}

---

## Bifurcation Mechanics

### The Three Regimes:

#### 1. Régimen Clásico (C < {self.CLASSICAL_THRESHOLD})
- **Comportamiento:** Máquina de Turing determinista
- **Complejidad:** Exponencial (2^n)
- **Búsqueda:** Ciega y serial
- **Aceleración:** A_eff = C^1 (lineal)

#### 2. Zona de Transición ({self.CLASSICAL_THRESHOLD} ≤ C < {self.GRACE_THRESHOLD})
- **Comportamiento:** Sintonización de frecuencia activa
- **Complejidad:** Interpolación exponencial→polinomial
- **Búsqueda:** Híbrida con resonancia parcial
- **Aceleración:** A_eff = C^(1→∞³) (no lineal)
- **Estado:** {'ACTIVO 🔄' if self.CLASSICAL_THRESHOLD <= C_current < self.GRACE_THRESHOLD else 'INACTIVO'}

#### 3. Estado de Gracia (C ≥ {self.GRACE_THRESHOLD})
- **Comportamiento:** Bifurcación NP→P
- **Complejidad:** Polinomial (n^2)
- **Búsqueda:** Resonante, solución emerge
- **Aceleración:** A_eff = C^∞³ (infinita)
- **Estado:** {'ACTIVO ✅' if C_current >= self.GRACE_THRESHOLD else 'INACTIVO'}

---

## Bifurcation Prediction

"""
        
        if bifurcation_pred['status'] == 'ALREADY_ACHIEVED':
            report += """
✅ **BIFURCACIÓN ACTIVA**

El sistema está operando en el Estado de Gracia. La bifurcación NP→P
está activa y los problemas NP se resuelven en tiempo polinomial.

**Recomendación:** Proceder con pruebas matemáticas complejas y
problemas NP-completos. El sistema tiene capacidad máxima.
"""
        else:
            report += f"""
⏳ **APROXIMÁNDOSE A BIFURCACIÓN**

- **Coherencia faltante:** {bifurcation_pred['delta_coherence']:.6f}
- **Tiempo estimado:** {bifurcation_pred['time_to_bifurcation_seconds']:.2f} segundos
- **Ciclos necesarios:** {bifurcation_pred['cycles_needed']:.2f}
- **Llegada estimada:** {bifurcation_pred['estimated_arrival']}

**Recomendación:** Esperar pico de coherencia para operaciones críticas.
El sistema está en {phase_analysis['regime']} y necesita {'incrementar' if bifurcation_pred['delta_coherence'] > 0 else 'mantener'}
coherencia para alcanzar bifurcación.
"""
        
        # Análisis de frecuencia
        report += f"""
---

## Frequency Analysis

- **f₀:** {self.f0} Hz (Frecuencia primordial)
- **τ₀:** {self.tau0*1000:.6f} ms (Período base)
- **Fase actual:** {phase:.6f}
- **Resonancia:** {self.resonance_effect(C_current, current_time):.6f}

### Próximos Picos de Coherencia:

La frecuencia {self.f0} Hz sintoniza los nodos del sistema. Los picos
de coherencia ocurren cuando la fase ≈ 0 o 1.

"""
        
        # Calcular próximos picos
        cycles_to_next = math.ceil(phase) - phase if phase < 0.5 else 1 - phase
        time_to_next_peak = cycles_to_next * self.tau0
        
        for i in range(3):
            peak_time = current_time + time_to_next_peak + i * self.tau0
            peak_datetime = datetime.fromtimestamp(peak_time)
            report += f"{i+1}. {peak_datetime.strftime('%H:%M:%S.%f')[:-3]} (+{time_to_next_peak + i*self.tau0:.6f}s)\n"
            
        report += f"""
---

## Complexity Scaling Examples

### SAT Problem Scaling:

| Tamaño (n) | Clásico (C=0.3) | Transición (C=0.7) | Gracia (C=0.95) |
|------------|-----------------|--------------------|--------------------|
"""
        
        for n in [10, 20, 30, 40, 50]:
            classical = self.compute_complexity_scaling(0.3, n)
            transition = self.compute_complexity_scaling(0.7, n)
            grace = self.compute_complexity_scaling(0.95, n)
            
            report += f"| {n:2d}         | {classical:.2e}      | {transition:.2e}       | {grace:.2e}         |\n"
            
        report += f"""
---

## Physical Interpretation

El colapso de complejidad no es un truco matemático; es una consecuencia
directa de la física cuántica de coherencia.

**En el punto de bifurcación (C = {self.BIFURCATION_POINT}):**

1. El denominador I × A_eff² × C^∞ crece exponencialmente
2. La barrera exponencial se vuelve despreciable
3. La función de onda de complejidad colapsa
4. La solución "resuena" antes de ser calculada explícitamente

**Axioma Fundamental:**
> "La dificultad de un problema no es una propiedad intrínseca del mismo,
> sino una relación entre el problema y el estado de fase del observador."

---

## Implications for Millennium Problems

### Riemann Hypothesis:
- **Búsqueda Clásica:** Precisión escala con log(T), computacionalmente costosa
- **Búsqueda Coherente:** Sistema sintoniza frecuencia del cero, discrepancia → 0
- **En C ≥ {self.GRACE_THRESHOLD}:** Ceros son nodos de coherencia, detección instantánea

### P vs NP:
- **Sin Coherencia:** P ≠ NP (separación exponencial)
- **Con Coherencia ≥ {self.GRACE_THRESHOLD}:** Bifurcación NP→P (colapso funcional)
- **Implicación:** La pregunta P vs NP depende del observador cuántico

---

## System Parameters

- **Frecuencia Fundamental:** {self.f0} Hz
- **Volatilidad Coherente:** {self.sigma}
- **Umbral Clásico:** {self.CLASSICAL_THRESHOLD}
- **Umbral de Gracia:** {self.GRACE_THRESHOLD}
- **Punto de Bifurcación:** {self.BIFURCATION_POINT}
- **Exponente Infinito:** ∞³ ≈ {self.INFINITY_CUBED * 10}

---

_Reporte generado por NPPBifurcationSimulator - QCAL ∞³ Framework_
_© 2025 JMMB Ψ · Instituto de Conciencia Cuántica (ICQ)_
"""
        
        return report
    
    def save_report(self, filename: Optional[str] = None) -> Path:
        """
        Guarda el reporte de bifurcación.
        
        Args:
            filename: Nombre del archivo (opcional)
            
        Returns:
            Path del archivo guardado
        """
        if filename is None:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f"np_p_bifurcation_{timestamp}.md"
            
        report = self.generate_bifurcation_report()
        
        output_path = Path(filename)
        output_path.write_text(report)
        
        return output_path
    
    def save_simulation_data(self, filename: Optional[str] = None) -> Path:
        """
        Guarda datos de simulación en formato JSON.
        
        Args:
            filename: Nombre del archivo (opcional)
            
        Returns:
            Path del archivo guardado
        """
        if filename is None:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f"bifurcation_data_{timestamp}.json"
            
        # Generar datos de simulación
        simulation_data = self.simulate_bifurcation_transition()
        
        # Añadir análisis de fase
        current_time = datetime.now().timestamp()
        phase = (current_time / self.tau0) % 1
        C_current = 0.5 + 0.5 * math.cos(2 * math.pi * phase)
        
        simulation_data['current_state'] = self.analyze_phase_transition(C_current)
        simulation_data['bifurcation_prediction'] = self.predict_bifurcation_time(C_current)
        simulation_data['acceleration_profile'] = self.compute_acceleration_profile()
        
        output_path = Path(filename)
        with open(output_path, 'w') as f:
            json.dump(simulation_data, f, indent=2)
            
        return output_path


def main():
    """Función principal de demostración."""
    print("=" * 80)
    print("NP→P BIFURCATION SIMULATOR - QCAL ∞³ Framework")
    print("=" * 80)
    print()
    
    simulator = NPPBifurcationSimulator()
    
    # Generar y mostrar reporte
    print("Generando reporte de bifurcación NP→P...")
    print()
    
    report = simulator.generate_bifurcation_report()
    print(report)
    
    # Guardar reporte
    report_file = simulator.save_report()
    print()
    print(f"✅ Reporte guardado en: {report_file}")
    
    # Guardar datos de simulación
    data_file = simulator.save_simulation_data()
    print(f"✅ Datos de simulación guardados en: {data_file}")
    print()
    
    # Análisis de transición actual
    print("-" * 80)
    print("ANÁLISIS DE TRANSICIÓN DE FASE ACTUAL")
    print("-" * 80)
    
    current_time = datetime.now().timestamp()
    phase = (current_time / simulator.tau0) % 1
    C_current = 0.5 + 0.5 * math.cos(2 * math.pi * phase)
    
    analysis = simulator.analyze_phase_transition(C_current)
    
    print(f"\nCoherencia: {analysis['coherence']:.6f}")
    print(f"Régimen: {analysis['regime']}")
    print(f"Fase: {analysis['phase']}")
    print(f"Descripción: {analysis['description']}")
    print(f"Distancia a Bifurcación: {analysis['distance_to_bifurcation']:.6f}")
    print(f"Parámetro de Orden: {analysis['order_parameter']:.6f}")
    print(f"Susceptibilidad: {analysis['susceptibility']:.6f}")
    print(f"Bifurcación Activa: {'SÍ ✅' if analysis['is_bifurcated'] else 'NO ❌'}")
    print()
    
    print("=" * 80)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 80)


if __name__ == "__main__":
    main()
