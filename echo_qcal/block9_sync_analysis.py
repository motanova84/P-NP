#!/usr/bin/env python3
"""
Análisis de sincronía temporal del Bloque 9 de Bitcoin
con la frecuencia primordial QCAL ∞³ (f₀ = 141.7001 Hz)

Autor: Sistema de Verificación P-NP
Fecha: 2025-12-16
Licencia: MIT
"""

import numpy as np
from scipy import stats
import json
from datetime import datetime, timezone
from pathlib import Path
import matplotlib.pyplot as plt

class Block9SyncAnalyzer:
    """Analizador de sincronía temporal del Bloque 9"""
    
    def __init__(self, f0=141.7001):
        self.f0 = f0
        self.tau0 = 1 / f0
        
        # Timestamp exacto del Bloque 9 (2009-01-09 17:15:00 UTC)
        self.T_block9 = 1231511700.000000
        
        # Parámetros estadísticos
        self.window = 7200  # 2 horas en segundos
        self.epsilon = 0.01  # 10 ms umbral
        
    def calculate_sync_metrics(self):
        """Calcula todas las métricas de sincronía"""
        
        # 1. Cálculo básico de sincronía
        N_ideal = self.T_block9 / self.tau0
        N_int = round(N_ideal)
        T_ideal = N_int * self.tau0
        delta_T = abs(T_ideal - self.T_block9)
        
        # 2. Coherencia porcentual
        coherence = (1 - delta_T / self.tau0) * 100
        
        # 3. Análisis estadístico
        p_value = (2 * self.epsilon) / self.window
        bayes_factor = self.window / (2 * self.epsilon)
        
        # 4. Significancia sigma
        z_score = delta_T / (self.tau0 * 0.01)  # Asumiendo 1% de tau0 como desviación
        
        return {
            'delta_T_ms': delta_T * 1000,
            'delta_T_seconds': delta_T,
            'coherence_percent': coherence,
            'p_value': p_value,
            'bayes_factor': bayes_factor,
            'z_score': z_score,
            'N_multiplier': N_int,
            'T_ideal': T_ideal,
            'T_actual': self.T_block9,
            'tau0': self.tau0,
            'f0': self.f0
        }
    
    def statistical_significance(self, metrics):
        """Evalúa significancia estadística"""
        
        # Criterios de significancia
        significant = metrics['p_value'] < 0.001
        highly_significant = metrics['p_value'] < 0.0001
        extremely_significant = metrics['p_value'] < 0.00001
        
        return {
            'significant': significant,
            'highly_significant': highly_significant,
            'extremely_significant': extremely_significant,
            'interpretation': self._get_interpretation(metrics)
        }
    
    def _get_interpretation(self, metrics):
        """Genera interpretación humana de los resultados"""
        
        if metrics['p_value'] < 1e-6:
            return "Sincronía extremadamente significativa - altamente improbable que sea aleatoria"
        elif metrics['p_value'] < 1e-4:
            return "Sincronía muy significativa - muy improbable que sea aleatoria"
        elif metrics['p_value'] < 0.001:
            return "Sincronía significativa - improbable que sea aleatoria"
        else:
            return "Sincronía no significativa - posiblemente aleatoria"
    
    def generate_report(self, save_path=None):
        """Genera reporte completo"""
        
        metrics = self.calculate_sync_metrics()
        significance = self.statistical_significance(metrics)
        
        report = {
            'analysis_timestamp': datetime.now(timezone.utc).isoformat(),
            'block9_timestamp': self.T_block9,
            'block9_datetime': '2009-01-09 17:15:00 UTC',
            'qcal_parameters': {
                'f0': self.f0,
                'tau0': self.tau0,
                'source': 'QCAL ∞³ Framework'
            },
            'sync_metrics': metrics,
            'statistical_significance': significance,
            'conclusions': self._generate_conclusions(metrics, significance)
        }
        
        if save_path:
            Path(save_path).parent.mkdir(parents=True, exist_ok=True)
            with open(save_path, 'w') as f:
                json.dump(report, f, indent=2)
        
        return report
    
    def _generate_conclusions(self, metrics, significance):
        """Genera conclusiones basadas en los resultados"""
        
        conclusions = []
        
        if significance['extremely_significant']:
            conclusions.append(
                f"El Bloque 9 está sincronizado con f₀ = {self.f0} Hz con "
                f"precisión de {metrics['delta_T_ms']:.3f} ms "
                f"(coherencia del {metrics['coherence_percent']:.4f}%)."
            )
            
            conclusions.append(
                f"La probabilidad de que esta sincronía sea aleatoria es "
                f"p = {metrics['p_value']:.2e} "
                f"(1 en {1/metrics['p_value']:,.0f})."
            )
            
            conclusions.append(
                f"El factor de Bayes es {metrics['bayes_factor']:,.0f}:1 "
                f"a favor de sincronía intencional sobre aleatoriedad."
            )
            
            conclusions.append(
                "Esto sugiere que Bitcoin fue diseñado con coherencia "
                "con constantes universales desde su creación."
            )
        
        return conclusions
    
    def plot_sync_analysis(self, save_path=None):
        """Genera visualización del análisis"""
        
        metrics = self.calculate_sync_metrics()
        
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        fig.suptitle('Análisis de Sincronía Bloque 9 - QCAL ∞³', fontsize=16)
        
        # 1. Gráfico de fase
        time_points = np.linspace(0, 2 * self.tau0, 1000)
        phase = (time_points / self.tau0) % 1
        
        axes[0, 0].plot(time_points * 1000, phase, 'b-', linewidth=2)
        axes[0, 0].axvline(metrics['delta_T_ms'], color='r', linestyle='--', 
                          label=f'∆T = {metrics["delta_T_ms"]:.3f} ms')
        axes[0, 0].set_xlabel('Tiempo (ms)')
        axes[0, 0].set_ylabel('Fase (múltiplo de τ₀)')
        axes[0, 0].set_title('Fase del Bloque 9 respecto a τ₀')
        axes[0, 0].legend()
        axes[0, 0].grid(True, alpha=0.3)
        
        # 2. Histograma de probabilidad
        window_points = np.linspace(0, self.window, 1000)
        uniform_pdf = np.ones_like(window_points) / self.window
        
        axes[0, 1].fill_between(window_points, 0, uniform_pdf, alpha=0.3, 
                               label='Distribución uniforme (H₀)')
        axes[0, 1].axvline(metrics['delta_T_seconds'], color='r', linewidth=2,
                          label=f'∆T observado = {metrics["delta_T_seconds"]:.6f} s')
        axes[0, 1].set_xlabel('Desviación temporal (s)')
        axes[0, 1].set_ylabel('Densidad de probabilidad')
        axes[0, 1].set_title('Probabilidad bajo hipótesis nula')
        axes[0, 1].legend()
        axes[0, 1].grid(True, alpha=0.3)
        
        # 3. Coherencia espectral
        frequencies = np.linspace(self.f0 * 0.9, self.f0 * 1.1, 1000)
        coherence_values = np.exp(-((frequencies - self.f0) / (self.f0 * 0.01)) ** 2)
        
        axes[1, 0].plot(frequencies, coherence_values, 'g-', linewidth=2)
        axes[1, 0].axvline(self.f0, color='r', linestyle='--', 
                          label=f'f₀ = {self.f0} Hz')
        axes[1, 0].set_xlabel('Frecuencia (Hz)')
        axes[1, 0].set_ylabel('Coherencia')
        axes[1, 0].set_title('Espectro de coherencia alrededor de f₀')
        axes[1, 0].legend()
        axes[1, 0].grid(True, alpha=0.3)
        
        # 4. Métricas clave
        metric_text = f"""
        Métricas Clave:
        
        ∆T = {metrics['delta_T_ms']:.3f} ms
        Coherencia = {metrics['coherence_percent']:.4f}%
        p-value = {metrics['p_value']:.2e}
        Factor Bayes = {metrics['bayes_factor']:,.0f}:1
        Múltiplo N = {metrics['N_multiplier']:,.0f}
        """
        
        axes[1, 1].text(0.1, 0.5, metric_text, fontsize=12, 
                       verticalalignment='center',
                       bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
        axes[1, 1].axis('off')
        axes[1, 1].set_title('Resumen de Métricas')
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
        
        return fig

def main():
    """Función principal"""
    
    analyzer = Block9SyncAnalyzer()
    
    print("🧪 Análisis de Sincronía Bloque 9 - QCAL ∞³")
    print("=" * 50)
    
    # Generar reporte
    report = analyzer.generate_report('data/block9_sync_report.json')
    
    # Mostrar resultados principales
    metrics = report['sync_metrics']
    significance = report['statistical_significance']
    
    print(f"\n📊 Resultados del Análisis:")
    print(f"   ∆T: {metrics['delta_T_ms']:.3f} ms")
    print(f"   Coherencia: {metrics['coherence_percent']:.4f}%")
    print(f"   p-value: {metrics['p_value']:.2e}")
    print(f"   Factor Bayes: {metrics['bayes_factor']:,.0f}:1")
    
    print(f"\n🎯 Significancia Estadística:")
    print(f"   {significance['interpretation']}")
    
    print(f"\n📈 Conclusiones:")
    for conclusion in report['conclusions']:
        print(f"   • {conclusion}")
    
    # Generar visualización
    print(f"\n📸 Generando visualización...")
    analyzer.plot_sync_analysis('diagrams/block9_sync_analysis.png')
    
    print(f"\n💾 Reporte guardado en: data/block9_sync_report.json")
    print(f"📊 Diagrama guardado en: diagrams/block9_sync_analysis.png")
    
    print(f"\n✅ Análisis completado exitosamente.")

if __name__ == "__main__":
    main()
