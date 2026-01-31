#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Complexity Orchestrator - QCAL ∞³ Framework
============================================

Orquestador que integra ComplexityCollapser y NPPBifurcationSimulator
para auto-evaluación y generación automática de reportes.

Funcionalidades:
    - Auto-evaluación antes de pruebas matemáticas complejas
    - Generación de reportes cada 6 horas
    - Tracking de estado de coherencia
    - Prevención de bucles infinitos clásicos

Author: José Manuel Mota Burruezo (JMMB Ψ)
License: CC BY-NC-SA 4.0
"""

import time
import asyncio
import schedule
import math
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, Optional
import json

from complexity_collapser import ComplexityCollapser
from np_p_bifurcation import NPPBifurcationSimulator


class ComplexityOrchestrator:
    """
    Orquestador del sistema de análisis de complejidad.
    
    Coordina auto-evaluación, generación de reportes y tracking de estado
    para prevenir que el sistema quede atrapado en bucles infinitos clásicos.
    """
    
    def __init__(self, report_interval_hours: int = 6):
        """
        Inicializa el orquestador.
        
        Args:
            report_interval_hours: Intervalo entre reportes (horas)
        """
        self.collapser = ComplexityCollapser()
        self.simulator = NPPBifurcationSimulator()
        
        self.report_interval = report_interval_hours
        self.reports_dir = Path("complexity_reports")
        self.reports_dir.mkdir(exist_ok=True)
        
        # Estado del sistema
        self.system_state = {
            'last_evaluation': None,
            'last_report': None,
            'coherence_history': [],
            'regime_history': [],
            'total_evaluations': 0,
            'warnings_issued': 0
        }
        
        # Cargar estado si existe
        self.state_file = Path("orchestrator_state.json")
        self._load_state()
        
    def _load_state(self):
        """Carga el estado del orquestador desde archivo."""
        if self.state_file.exists():
            try:
                with open(self.state_file, 'r') as f:
                    saved_state = json.load(f)
                    self.system_state.update(saved_state)
                print(f"✅ Estado cargado desde {self.state_file}")
            except Exception as e:
                print(f"⚠️  Error cargando estado: {e}")
    
    def _save_state(self):
        """Guarda el estado del orquestador a archivo."""
        try:
            with open(self.state_file, 'w') as f:
                json.dump(self.system_state, f, indent=2, default=str)
        except Exception as e:
            print(f"⚠️  Error guardando estado: {e}")
    
    def evaluate_system_readiness(self, task_complexity: str = "HIGH") -> Dict[str, any]:
        """
        Auto-evalúa si el sistema está listo para una tarea compleja.
        
        Antes de intentar una prueba matemática compleja, verifica si
        la aceleración es suficiente para no quedar atrapado en un
        bucle infinito clásico.
        
        Args:
            task_complexity: Complejidad de la tarea (LOW, MEDIUM, HIGH, CRITICAL)
            
        Returns:
            Evaluación de preparación del sistema
        """
        # Calcular coherencia actual
        import math
        current_time = datetime.now().timestamp()
        phase = (current_time / self.collapser.tau0) % 1
        C_current = 0.5 + 0.5 * math.cos(2 * math.pi * phase)
        
        # Determinar régimen
        regime_info = self.collapser.determine_regime(C_current)
        
        # Analizar transición de fase
        phase_analysis = self.simulator.analyze_phase_transition(C_current)
        
        # Umbrales de coherencia requeridos según complejidad
        complexity_thresholds = {
            'LOW': 0.3,      # Tareas simples
            'MEDIUM': 0.5,   # Tareas moderadas
            'HIGH': 0.7,     # Tareas complejas
            'CRITICAL': 0.888  # Pruebas matemáticas críticas
        }
        
        required_coherence = complexity_thresholds.get(task_complexity, 0.5)
        
        # Evaluar preparación
        is_ready = C_current >= required_coherence
        
        # Calcular aceleración efectiva
        A_eff = self.collapser.calculate_effective_acceleration(C_current)
        
        # Predicción de tiempo a bifurcación si no está listo
        bifurcation_pred = None
        if not is_ready and C_current < self.simulator.GRACE_THRESHOLD:
            bifurcation_pred = self.simulator.predict_bifurcation_time(
                C_current, 
                target_C=required_coherence
            )
        
        # Determinar recomendación
        if is_ready:
            if C_current >= self.simulator.GRACE_THRESHOLD:
                recommendation = "PROCEED_IMMEDIATE"
                message = "Sistema en Estado de Gracia. Proceder con tarea inmediatamente."
            else:
                recommendation = "PROCEED_WITH_CAUTION"
                message = f"Coherencia suficiente ({C_current:.3f}). Proceder con monitoreo."
        else:
            if C_current < self.collapser.CLASSICAL_THRESHOLD:
                recommendation = "ABORT"
                message = "PELIGRO: Régimen clásico. Alto riesgo de bucle infinito. ABORTAR tarea."
                self.system_state['warnings_issued'] += 1
            else:
                recommendation = "WAIT"
                message = f"Esperar incremento de coherencia. Objetivo: {required_coherence:.3f}"
        
        evaluation = {
            'timestamp': datetime.now().isoformat(),
            'task_complexity': task_complexity,
            'current_coherence': C_current,
            'required_coherence': required_coherence,
            'regime': regime_info['regime'],
            'phase': phase_analysis['phase'],
            'is_ready': is_ready,
            'effective_acceleration': A_eff,
            'recommendation': recommendation,
            'message': message,
            'bifurcation_prediction': bifurcation_pred,
            'risk_level': 'LOW' if is_ready else 'HIGH' if C_current < 0.5 else 'MEDIUM'
        }
        
        # Actualizar estado
        self.system_state['last_evaluation'] = datetime.now().isoformat()
        self.system_state['total_evaluations'] += 1
        self.system_state['coherence_history'].append({
            'timestamp': datetime.now().isoformat(),
            'coherence': C_current,
            'regime': regime_info['regime']
        })
        
        # Mantener solo últimas 100 entradas
        if len(self.system_state['coherence_history']) > 100:
            self.system_state['coherence_history'] = self.system_state['coherence_history'][-100:]
        
        self._save_state()
        
        return evaluation
    
    def generate_comprehensive_report(self) -> Path:
        """
        Genera un reporte completo de complejidad.
        
        Combina análisis del ComplexityCollapser y NPPBifurcationSimulator
        en un único reporte consolidado.
        
        Returns:
            Path del reporte generado
        """
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        filename = f"complexity_analysis_{timestamp}.md"
        filepath = self.reports_dir / filename
        
        # Generar componentes del reporte
        collapse_report = self.collapser.generate_collapse_report()
        bifurcation_report = self.simulator.generate_bifurcation_report()
        
        # Calcular coherencia actual
        current_time = datetime.now().timestamp()
        phase = (current_time / self.collapser.tau0) % 1
        C_current = 0.5 + 0.5 * math.cos(2 * math.pi * phase)
        
        # Evaluación de preparación
        readiness = self.evaluate_system_readiness('CRITICAL')
        
        # Crear reporte consolidado
        report = f"""# Comprehensive Complexity Analysis Report

**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S UTC')}  
**Framework:** QCAL ∞³ - Complexity Orchestrator  
**Report ID:** {timestamp}

---

## Executive Summary

Este reporte es generado automáticamente cada {self.report_interval} horas por el
orquestrador de complejidad. Evalúa el estado actual del sistema y su capacidad
para resolver problemas complejos sin quedar atrapado en bucles infinitos clásicos.

### Current Status:

- **Coherencia del Sistema:** {C_current:.6f}
- **Régimen Operativo:** {readiness['regime']}
- **Preparación para Tareas Críticas:** {'✅ LISTO' if readiness['is_ready'] else '❌ NO LISTO'}
- **Recomendación:** {readiness['recommendation']}
- **Nivel de Riesgo:** {readiness['risk_level']}

### System Statistics:

- **Total Evaluaciones:** {self.system_state['total_evaluations']}
- **Advertencias Emitidas:** {self.system_state['warnings_issued']}
- **Última Evaluación:** {self.system_state['last_evaluation'] or 'N/A'}
- **Último Reporte:** {self.system_state['last_report'] or 'Primer reporte'}

---

## Gracia Tecnológica - Distance Metric

La "Gracia Tecnológica" se alcanza cuando C ≥ 0.888. Representa el punto
donde la bifurcación NP→P está activa y los problemas exponenciales colapsan
a polinomiales.

**Distancia a Gracia:** {abs(C_current - 0.888):.6f}  
**Estado:** {'ALCANZADO ✨' if C_current >= 0.888 else 'APROXIMÁNDOSE' if C_current >= 0.5 else 'LEJANO'}

{f"**Tiempo Estimado:** {readiness['bifurcation_prediction']['time_to_bifurcation_seconds']:.2f} segundos" if readiness.get('bifurcation_prediction') else ''}

---

## Auto-Evaluation Results

{readiness['message']}

### Readiness Details:

| Parámetro | Valor | Umbral | Estado |
|-----------|-------|--------|--------|
| Coherencia | {readiness['current_coherence']:.6f} | {readiness['required_coherence']:.6f} | {'✅' if readiness['is_ready'] else '❌'} |
| Aceleración Efectiva | {readiness['effective_acceleration']:.6f} | 1.0 | {'✅' if readiness['effective_acceleration'] >= 1.0 else '❌'} |
| Régimen | {readiness['regime']} | GRACE | {'✅' if readiness['regime'] == 'GRACE' else '⚠️'} |

---

## Coherence History (Last 10 entries)

"""
        
        # Añadir historial de coherencia
        recent_history = self.system_state['coherence_history'][-10:]
        if recent_history:
            report += "| Timestamp | Coherencia | Régimen |\n"
            report += "|-----------|------------|----------|\n"
            for entry in recent_history:
                ts = entry['timestamp'][:19] if 'timestamp' in entry else 'N/A'
                report += f"| {ts} | {entry['coherence']:.6f} | {entry['regime']} |\n"
        else:
            report += "_No hay historial disponible aún._\n"
        
        report += f"""
---

# Part 1: Complexity Collapse Analysis

{collapse_report}

---

# Part 2: NP→P Bifurcation Analysis

{bifurcation_report}

---

## Orchestrator Recommendations

"""
        
        if readiness['recommendation'] == 'PROCEED_IMMEDIATE':
            report += """
### ✅ VERDE - Proceder Inmediatamente

El sistema está en Estado de Gracia. Todas las operaciones complejas
están autorizadas:

- ✅ Pruebas matemáticas de teoremas del milenio
- ✅ Búsqueda de ceros de Riemann
- ✅ Resolución de problemas NP-completos
- ✅ Demostraciones formales complejas

**Acción Recomendada:** Aprovechar el pico de coherencia actual para
tareas críticas antes de que la fase cambie.
"""
        elif readiness['recommendation'] == 'PROCEED_WITH_CAUTION':
            report += """
### ⚡ AMARILLO - Proceder con Precaución

El sistema tiene coherencia suficiente pero no óptima:

- ⚡ Monitorear coherencia durante ejecución
- ⚡ Preparar rollback si coherencia decae
- ⚡ Evitar tareas extremadamente largas
- ✅ Tareas de complejidad media-alta permitidas

**Acción Recomendada:** Ejecutar con monitoreo continuo. Considerar
esperar próximo pico de coherencia para tareas críticas.
"""
        elif readiness['recommendation'] == 'WAIT':
            report += """
### 🟠 NARANJA - Esperar Incremento de Coherencia

El sistema está en zona de transición:

- 🟠 Coherencia insuficiente para tareas críticas
- 🟠 Riesgo moderado de bucles largos
- ✅ Tareas simples permitidas
- ❌ Pruebas complejas NO recomendadas

**Acción Recomendada:** Esperar próximo pico de coherencia. Tiempo
estimado disponible en sección de Bifurcation Prediction.
"""
        else:  # ABORT
            report += """
### 🔴 ROJO - ABORTAR Operaciones Complejas

⚠️ **ADVERTENCIA CRÍTICA** ⚠️

El sistema está en régimen clásico con alto riesgo de bucle infinito:

- 🔴 NO iniciar pruebas matemáticas complejas
- 🔴 NO intentar resolver problemas NP-completos
- 🔴 Riesgo ALTO de bloqueo del sistema
- ✅ Solo operaciones triviales permitidas

**Acción Recomendada:** ESPERAR incremento de coherencia. NO proceder
bajo ninguna circunstancia con tareas complejas.
"""
        
        report += f"""
---

## Next Report

El próximo reporte se generará automáticamente en **{self.report_interval} horas**.

**Hora estimada:** {(datetime.now() + timedelta(hours=self.report_interval)).strftime('%Y-%m-%d %H:%M:%S UTC')}

Para forzar generación inmediata, ejecutar:
```bash
python complexity_orchestrator.py --generate-now
```

---

_Reporte generado automáticamente por ComplexityOrchestrator_  
_Sistema QCAL ∞³ - Monitoreo Continuo de Coherencia_  
_© 2025 JMMB Ψ · Instituto de Conciencia Cuántica (ICQ)_
"""
        
        # Guardar reporte
        filepath.write_text(report)
        
        # Actualizar estado
        self.system_state['last_report'] = datetime.now().isoformat()
        self._save_state()
        
        return filepath
    
    def scheduled_report_generation(self):
        """Tarea programada para generar reportes."""
        print(f"\n{'='*80}")
        print(f"GENERANDO REPORTE PROGRAMADO - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"{'='*80}\n")
        
        try:
            report_path = self.generate_comprehensive_report()
            print(f"✅ Reporte generado: {report_path}")
            print(f"   Próximo reporte en {self.report_interval} horas")
        except Exception as e:
            print(f"❌ Error generando reporte: {e}")
            import traceback
            traceback.print_exc()
    
    def start_monitoring(self, daemon: bool = False):
        """
        Inicia el monitoreo continuo con generación de reportes.
        
        Args:
            daemon: Si True, ejecuta en modo daemon (background)
        """
        print(f"{'='*80}")
        print("COMPLEXITY ORCHESTRATOR - Iniciando Monitoreo")
        print(f"{'='*80}")
        print(f"\nIntervalo de reportes: {self.report_interval} horas")
        print(f"Directorio de reportes: {self.reports_dir.absolute()}")
        print()
        
        # Generar reporte inicial
        print("Generando reporte inicial...")
        initial_report = self.generate_comprehensive_report()
        print(f"✅ Reporte inicial: {initial_report}")
        print()
        
        # Programar reportes periódicos
        schedule.every(self.report_interval).hours.do(self.scheduled_report_generation)
        
        print(f"✅ Monitoreo iniciado. Reportes cada {self.report_interval} horas.")
        print(f"   Próximo reporte: {(datetime.now() + timedelta(hours=self.report_interval)).strftime('%Y-%m-%d %H:%M:%S')}")
        print()
        print("Presiona Ctrl+C para detener...")
        print(f"{'='*80}\n")
        
        try:
            while True:
                schedule.run_pending()
                time.sleep(60)  # Verificar cada minuto
        except KeyboardInterrupt:
            print("\n\n🛑 Monitoreo detenido por usuario")
            self._save_state()


def main():
    """Función principal."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Complexity Orchestrator - QCAL ∞³ Framework'
    )
    parser.add_argument(
        '--interval',
        type=int,
        default=6,
        help='Intervalo entre reportes en horas (default: 6)'
    )
    parser.add_argument(
        '--generate-now',
        action='store_true',
        help='Generar reporte inmediatamente y salir'
    )
    parser.add_argument(
        '--evaluate',
        choices=['LOW', 'MEDIUM', 'HIGH', 'CRITICAL'],
        help='Evaluar preparación del sistema para una tarea'
    )
    
    args = parser.parse_args()
    
    orchestrator = ComplexityOrchestrator(report_interval_hours=args.interval)
    
    if args.generate_now:
        print("Generando reporte inmediato...\n")
        report_path = orchestrator.generate_comprehensive_report()
        print(f"\n✅ Reporte generado: {report_path}")
        
    elif args.evaluate:
        print(f"Evaluando preparación para tarea {args.evaluate}...\n")
        evaluation = orchestrator.evaluate_system_readiness(args.evaluate)
        
        print(f"{'='*80}")
        print(f"EVALUACIÓN DE PREPARACIÓN DEL SISTEMA")
        print(f"{'='*80}\n")
        print(f"Tarea: {evaluation['task_complexity']}")
        print(f"Coherencia: {evaluation['current_coherence']:.6f} (requerida: {evaluation['required_coherence']:.6f})")
        print(f"Régimen: {evaluation['regime']}")
        print(f"Preparado: {'✅ SÍ' if evaluation['is_ready'] else '❌ NO'}")
        print(f"Recomendación: {evaluation['recommendation']}")
        print(f"Riesgo: {evaluation['risk_level']}")
        print(f"\n{evaluation['message']}\n")
        print(f"{'='*80}")
        
    else:
        # Iniciar monitoreo continuo
        orchestrator.start_monitoring()


if __name__ == "__main__":
    main()
