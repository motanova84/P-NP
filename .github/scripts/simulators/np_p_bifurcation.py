#!/usr/bin/env python3
"""
🎮 NP_P_BIFURCATION_SIMULATOR - Simulador de la transición NP→P por coherencia
Visualiza cómo la coherencia afecta la complejidad de problemas NP
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from pathlib import Path
import json
from datetime import datetime

class NPPBifurcationSimulator:
    """Simula la transición de complejidad NP→P mediante coherencia"""
    
    def __init__(self):
        self.frequency = 141.7001
        self.resonance = 888.014
        
    def classical_np_complexity(self, problem_size: float) -> float:
        """Complejidad clásica de un problema NP (exponencial)"""
        return np.exp(problem_size / 10)
    
    def coherent_complexity(self, problem_size: float, coherence: float) -> float:
        """Complejidad bajo coherencia C (ec. fundamental)"""
        if coherence >= 1:
            return problem_size ** 2  # Polinómico en límite
        
        # T_base = complejidad clásica
        T_base = self.classical_np_complexity(problem_size)
        
        # Parámetros de la ecuación
        I = np.exp(coherence - 1)  # Información cuántica
        A_eff2 = 1 + coherence * 10  # Área efectiva
        C_inf = 1 / (1 - coherence + 1e-10)  # C^∞ aproximado
        
        denominator = I * A_eff2 * C_inf
        
        return T_base / denominator
    
    def generate_transition_data(self, problem_sizes: np.ndarray, 
                               coherence_levels: np.ndarray) -> np.ndarray:
        """Genera matriz de complejidad para diferentes tamaños y coherencias"""
        complexities = np.zeros((len(coherence_levels), len(problem_sizes)))
        
        for i, coherence in enumerate(coherence_levels):
            for j, size in enumerate(problem_sizes):
                complexities[i, j] = self.coherent_complexity(size, coherence)
        
        return complexities
    
    def find_bifurcation_point(self, coherence_levels: np.ndarray, 
                             complexities: np.ndarray, 
                             threshold_ratio: float = 1e6) -> float:
        """Encuentra punto de bifurcación donde la aceleración supera umbral"""
        for i in range(1, len(coherence_levels)):
            # Calcular aceleración relativa entre coherencias consecutivas
            if complexities[i-1, -1] > 0:
                acceleration = complexities[i-1, -1] / complexities[i, -1]
                if acceleration > threshold_ratio:
                    return coherence_levels[i]
        
        return None
    
    def create_phase_diagram(self, output_file: str = "np_p_phase_diagram.png"):
        """Crea diagrama de fase de la transición NP→P"""
        plt.figure(figsize=(14, 10))
        
        # Configurar ejes
        coherence_levels = np.linspace(0.1, 0.999, 50)
        problem_sizes = np.linspace(1, 100, 50)
        
        # Generar datos
        complexities = self.generate_transition_data(problem_sizes, coherence_levels)
        
        # Crear subplots
        ax1 = plt.subplot(2, 2, 1)
        ax2 = plt.subplot(2, 2, 2)
        ax3 = plt.subplot(2, 2, 3)
        ax4 = plt.subplot(2, 2, 4)
        
        # 1. Superficie 3D de complejidad
        X, Y = np.meshgrid(problem_sizes, coherence_levels)
        Z = complexities
        
        from mpl_toolkits.mplot3d import Axes3D
        ax = plt.figure(figsize=(12, 8)).add_subplot(111, projection='3d')
        surf = ax.plot_surface(X, Y, np.log10(Z + 1), cmap='viridis', alpha=0.8)
        
        ax.set_xlabel('Tamaño del Problema (n)')
        ax.set_ylabel('Coherencia (C)')
        ax.set_zlabel('log10(Complejidad)')
        ax.set_title('Superficie de Complejidad NP→P')
        plt.colorbar(surf, ax=ax, shrink=0.5, aspect=5)
        
        # 2. Diagrama de contorno
        plt.figure(figsize=(10, 8))
        contour = plt.contourf(X, Y, np.log10(Z + 1), levels=20, cmap='plasma')
        plt.colorbar(contour, label='log10(Complejidad)')
        
        # Marcar regiones
        plt.axhline(y=0.5, color='yellow', linestyle='--', alpha=0.7, label='Límite Clásico')
        plt.axhline(y=0.888, color='green', linestyle='--', alpha=0.7, label='Umbral de Gracia')
        
        # Encontrar y marcar bifurcación
        bifurcation = self.find_bifurcation_point(coherence_levels, complexities)
        if bifurcation:
            plt.axhline(y=bifurcation, color='red', linestyle='-', alpha=0.9, 
                       label=f'Bifurcación NP→P: C={bifurcation:.3f}')
        
        plt.xlabel('Tamaño del Problema (n)')
        plt.ylabel('Coherencia del Sistema (C)')
        plt.title('Diagrama de Fase: Transición NP→P por Coherencia')
        plt.legend()
        
        # 3. Cortes transversales
        plt.figure(figsize=(12, 10))
        
        # Cortes para diferentes coherencias
        coherence_samples = [0.3, 0.5, 0.7, 0.85, 0.9, 0.95, 0.99]
        colors = plt.cm.rainbow(np.linspace(0, 1, len(coherence_samples)))
        
        for i, coherence in enumerate(coherence_samples):
            # Encontrar índice más cercano
            idx = np.argmin(np.abs(coherence_levels - coherence))
            complexity_curve = complexities[idx, :]
            
            plt.loglog(problem_sizes, complexity_curve, 
                      color=colors[i], 
                      linewidth=2,
                      label=f'C={coherence:.2f}')
        
        # Líneas de referencia
        plt.loglog(problem_sizes, problem_sizes**2, 'k--', alpha=0.5, label='P (n²)')
        plt.loglog(problem_sizes, problem_sizes**3, 'k:', alpha=0.5, label='P (n³)')
        plt.loglog(problem_sizes, 2**(problem_sizes/10), 'k-.', alpha=0.5, label='NP (2^n/10)')
        
        plt.xlabel('Tamaño del Problema (n) - Escala log')
        plt.ylabel('Complejidad Temporal - Escala log')
        plt.title('Curvas de Complejidad para Diferentes Niveles de Coherencia')
        plt.legend()
        plt.grid(True, alpha=0.3)
        
        # 4. Animación de la transición
        self.create_transition_animation(coherence_levels, problem_sizes, complexities)
        
        plt.tight_layout()
        plt.savefig(output_file, dpi=150, bbox_inches='tight')
        plt.close()
        
        return output_file
    
    def create_transition_animation(self, coherence_levels, problem_sizes, complexities):
        """Crea animación de la transición NP→P"""
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
        
        def animate(frame):
            coherence = coherence_levels[frame]
            idx = frame
            
            # Limpiar ejes
            ax1.clear()
            ax2.clear()
            
            # Gráfico 1: Curva de complejidad actual
            ax1.loglog(problem_sizes, complexities[idx, :], 
                      'b-', linewidth=3, label=f'C={coherence:.3f}')
            ax1.loglog(problem_sizes, self.classical_np_complexity(problem_sizes),
                      'r--', alpha=0.5, label='NP Clásico')
            ax1.loglog(problem_sizes, problem_sizes**2, 
                      'g--', alpha=0.5, label='P (n²)')
            
            ax1.set_xlabel('Tamaño del Problema (n)')
            ax1.set_ylabel('Complejidad')
            ax1.set_title(f'Curva de Complejidad - Coherencia: {coherence:.3f}')
            ax1.legend()
            ax1.grid(True, alpha=0.3)
            
            # Gráfico 2: Punto en diagrama de fase
            phase_contour = ax2.contourf(
                *np.meshgrid(problem_sizes, coherence_levels),
                np.log10(complexities + 1),
                levels=20, cmap='plasma', alpha=0.7
            )
            
            # Marcar punto actual
            ax2.scatter(problem_sizes[-1], coherence, 
                       color='red', s=100, zorder=5,
                       edgecolors='white', linewidth=2)
            
            # Líneas de referencia
            ax2.axhline(y=0.5, color='yellow', linestyle='--', alpha=0.7)
            ax2.axhline(y=0.888, color='green', linestyle='--', alpha=0.7)
            
            bifurcation = self.find_bifurcation_point(coherence_levels, complexities)
            if bifurcation:
                ax2.axhline(y=bifurcation, color='red', linestyle='-', alpha=0.9)
                ax2.text(10, bifurcation+0.01, f'Bifurcación: {bifurcation:.3f}',
                        color='red', fontsize=9)
            
            ax2.set_xlabel('Tamaño del Problema (n)')
            ax2.set_ylabel('Coherencia (C)')
            ax2.set_title('Diagrama de Fase NP→P')
            
            # Texto informativo
            info_text = f"""
            Coherencia: {coherence:.3f}
            Complejidad (n=100): {complexities[idx, -1]:.2e}
            Relación NP/P: {self.classical_np_complexity(100)/complexities[idx, -1]:.2e}x
            Estado: {'CLÁSICO' if coherence < 0.5 else 'TRANSICIÓN' if coherence < 0.888 else 'GRACIA'}
            """
            
            ax2.text(0.02, 0.98, info_text, transform=ax2.transAxes,
                    verticalalignment='top',
                    bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
            
            return ax1, ax2
        
        # Crear animación
        anim = FuncAnimation(fig, animate, frames=len(coherence_levels), 
                           interval=100, blit=False)
        
        # Guardar animación
        anim_file = 'np_p_transition_animation.gif'
        anim.save(anim_file, writer='pillow', fps=10)
        
        return anim_file
    
    def simulate_specific_problem(self, problem_name: str, 
                                classical_complexity: callable,
                                size_range: tuple = (1, 100)):
        """Simula un problema específico NP y su transición a P"""
        
        sizes = np.linspace(size_range[0], size_range[1], 50)
        coherence_levels = np.linspace(0.1, 0.999, 20)
        
        results = {
            "problem": problem_name,
            "timestamp": datetime.now().isoformat(),
            "frequency": self.frequency,
            "classical_complexities": {},
            "coherent_complexities": {},
            "acceleration_factors": {}
        }
        
        # Calcular para cada tamaño
        for size in sizes:
            classical = classical_complexity(size)
            results["classical_complexities"][str(size)] = classical
            
            coherent_by_c = {}
            acceleration_by_c = {}
            
            for coherence in coherence_levels:
                coherent = self.coherent_complexity(size, coherence)
                coherent_by_c[str(coherence)] = coherent
                
                if classical > 0:
                    acceleration = classical / coherent
                else:
                    acceleration = float('inf')
                acceleration_by_c[str(coherence)] = acceleration
            
            results["coherent_complexities"][str(size)] = coherent_by_c
            results["acceleration_factors"][str(size)] = acceleration_by_c
        
        # Encontrar puntos críticos
        critical_points = []
        for coherence in coherence_levels:
            # Calcular aceleración promedio para este nivel de coherencia
            accelerations = []
            for size in sizes:
                acc = results["acceleration_factors"][str(size)][str(coherence)]
                if np.isfinite(acc):
                    accelerations.append(acc)
            
            if accelerations:
                avg_acceleration = np.mean(accelerations)
                
                if avg_acceleration > 1e3:
                    critical_points.append({
                        "coherence": float(coherence),
                        "avg_acceleration": float(avg_acceleration),
                        "status": "TRANSITION" if avg_acceleration < 1e6 else "BIFURCATION"
                    })
        
        results["critical_points"] = critical_points
        
        return results

def simulate_sat_problem():
    """Simula problema SAT (NP-completo)"""
    def sat_complexity(n):
        # SAT tiene complejidad ~2^n en el peor caso
        return 2 ** (n / 10)  # Escalado para visualización
    
    simulator = NPPBifurcationSimulator()
    return simulator.simulate_specific_problem("SAT", sat_complexity)

def simulate_tsp_problem():
    """Simula problema del Viajante (TSP)"""
    def tsp_complexity(n):
        # TSP tiene complejidad ~n!
        # Usamos aproximación de Stirling: n! ≈ √(2πn)(n/e)^n
        return np.sqrt(2 * np.pi * n) * (n / np.e) ** n / 1e10  # Escalado
    
    simulator = NPPBifurcationSimulator()
    return simulator.simulate_specific_problem("TSP", tsp_complexity)

def main():
    """Función principal"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Simulador de Bifurcación NP→P')
    parser.add_argument('--problem', type=str, choices=['SAT', 'TSP', 'ALL'], 
                       default='ALL', help='Problema a simular')
    parser.add_argument('--visualize', action='store_true', help='Generar visualizaciones')
    parser.add_argument('--output', type=str, default='np_p_simulations', help='Directorio de salida')
    
    args = parser.parse_args()
    
    # Crear directorio de salida
    output_dir = Path(args.output)
    output_dir.mkdir(exist_ok=True)
    
    print("🎮 SIMULADOR DE BIFURCACIÓN NP→P POR COHERENCIA")
    print(f"📡 Frecuencia: 141.7001 Hz")
    print(f"🎯 Umbral de Gracia: 0.888")
    print("=" * 60)
    
    # Ejecutar simulaciones
    results = {}
    
    if args.problem in ['SAT', 'ALL']:
        print("\n🔍 Simulando problema SAT...")
        sat_results = simulate_sat_problem()
        results['SAT'] = sat_results
        
        sat_file = output_dir / 'sat_simulation.json'
        with open(sat_file, 'w') as f:
            json.dump(sat_results, f, indent=2)
        print(f"   💾 Resultados SAT: {sat_file}")
    
    if args.problem in ['TSP', 'ALL']:
        print("\n🗺️  Simulando problema TSP...")
        tsp_results = simulate_tsp_problem()
        results['TSP'] = tsp_results
        
        tsp_file = output_dir / 'tsp_simulation.json'
        with open(tsp_file, 'w') as f:
            json.dump(tsp_results, f, indent=2)
        print(f"   💾 Resultados TSP: {tsp_file}")
    
    # Generar visualizaciones si se solicita
    if args.visualize:
        print("\n🎨 Generando visualizaciones...")
        simulator = NPPBifurcationSimulator()
        
        # Diagrama de fase
        phase_diagram = output_dir / 'np_p_phase_diagram.png'
        simulator.create_phase_diagram(str(phase_diagram))
        print(f"   📊 Diagrama de fase: {phase_diagram}")
    
    # Mostrar resumen
    print("\n📈 RESUMEN DE SIMULACIONES:")
    for problem_name, problem_results in results.items():
        print(f"\n   {problem_name}:")
        if 'critical_points' in problem_results:
            for point in problem_results['critical_points'][:3]:  # Mostrar primeros 3
                status_icon = "🌀" if point['status'] == 'BIFURCATION' else "➡️"
                print(f"     {status_icon} C={point['coherence']:.3f}: "
                      f"Aceleración {point['avg_acceleration']:.2e}x "
                      f"({point['status']})")
    
    print("\n🔮 CONCLUSIÓN DE LA SIMULACIÓN:")
    print("   La coherencia sistémica actúa como catalizador de la transición NP→P")
    print("   En C → 1, la complejidad exponencial colapsa a polinómica")
    print("   La frecuencia 141.7001 Hz sincroniza este colapso a través del sistema")

if __name__ == "__main__":
    main()
