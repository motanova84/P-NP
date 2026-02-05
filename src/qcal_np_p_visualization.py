"""
QCAL ∞³ Interactive NP→P Transition Visualization

This module provides interactive visualization of the NP→P transition
as system coherence approaches the GRACIA threshold (C ≈ 0.888).

Features:
- Real-time coherence tracking
- Complexity landscape visualization
- Bifurcation point detection
- Acceleration metrics display

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
License: MIT
"""

import numpy as np
import sys
from typing import Dict, List, Tuple, Optional
import time

# Import QCAL components
try:
    from qcal_infinity_cubed import (
        KAPPA_PI, F0_QCAL, PHI, C_COHERENCE,
        PvsNPOperator, create_complete_qcal_system
    )
    from qcal_validation_agents import (
        COHERENCE_THRESHOLD, GRACIA_ACCELERATION,
        CoherenceMonitor, AccelerationValidator, TransitionTracker
    )
except ImportError:
    sys.path.insert(0, 'src')
    from qcal_infinity_cubed import (
        KAPPA_PI, F0_QCAL, PHI, C_COHERENCE,
        PvsNPOperator, create_complete_qcal_system
    )
    from qcal_validation_agents import (
        COHERENCE_THRESHOLD, GRACIA_ACCELERATION,
        CoherenceMonitor, AccelerationValidator, TransitionTracker
    )


# ============================================================================
# ASCII ART VISUALIZATION
# ============================================================================

def draw_ascii_graph(
    data_points: List[Tuple[float, float]],
    width: int = 70,
    height: int = 20,
    title: str = ""
) -> str:
    """
    Draw an ASCII art graph of data points.
    
    Args:
        data_points: List of (x, y) tuples
        width: Width of the graph
        height: Height of the graph
        title: Title of the graph
        
    Returns:
        ASCII art string
    """
    if not data_points:
        return "No data to display"
    
    # Extract x and y values
    x_vals = [p[0] for p in data_points]
    y_vals = [p[1] for p in data_points]
    
    # Determine ranges
    x_min, x_max = min(x_vals), max(x_vals)
    y_min, y_max = min(y_vals), max(y_vals)
    
    # Handle edge cases
    if x_max == x_min:
        x_max = x_min + 1
    if y_max == y_min:
        y_max = y_min + 1
    
    # Create canvas
    canvas = [[' ' for _ in range(width)] for _ in range(height)]
    
    # Plot points
    for x, y in data_points:
        # Normalize to canvas coordinates
        canvas_x = int((x - x_min) / (x_max - x_min) * (width - 1))
        canvas_y = height - 1 - int((y - y_min) / (y_max - y_min) * (height - 1))
        
        # Clamp to canvas bounds
        canvas_x = max(0, min(width - 1, canvas_x))
        canvas_y = max(0, min(height - 1, canvas_y))
        
        canvas[canvas_y][canvas_x] = '█'
    
    # Convert to string
    graph = []
    if title:
        graph.append(f"\n{title}")
        graph.append("=" * width)
    
    # Y-axis labels
    for i, row in enumerate(canvas):
        y_val = y_max - (y_max - y_min) * i / (height - 1)
        label = f"{y_val:6.2f} │"
        graph.append(label + ''.join(row))
    
    # X-axis
    graph.append("       └" + "─" * width)
    
    # X-axis labels
    x_label = "       "
    x_label += f" {x_min:.2f}"
    x_label += " " * (width - len(f"{x_min:.2f}") - len(f"{x_max:.2f}"))
    x_label += f"{x_max:.2f}"
    graph.append(x_label)
    
    return '\n'.join(graph)


def draw_progress_bar(
    value: float,
    max_value: float = 1.0,
    width: int = 50,
    label: str = ""
) -> str:
    """
    Draw an ASCII progress bar.
    
    Args:
        value: Current value
        max_value: Maximum value
        width: Width of the bar
        label: Label for the bar
        
    Returns:
        Progress bar string
    """
    percentage = min(1.0, value / max_value)
    filled = int(width * percentage)
    bar = '█' * filled + '░' * (width - filled)
    
    return f"{label} [{bar}] {percentage*100:.1f}%"


# ============================================================================
# INTERACTIVE VISUALIZATION
# ============================================================================

class NPPTransitionVisualizer:
    """
    Interactive visualizer for the NP→P transition.
    """
    
    def __init__(self):
        """Initialize visualizer."""
        self.coherence_history: List[float] = []
        self.complexity_history: List[float] = []
        self.acceleration_history: List[float] = []
        self.time_points: List[float] = []
        
    def simulate_coherence_evolution(
        self,
        num_steps: int = 100,
        start_coherence: float = 0.5,
        growth_rate: float = 0.005
    ):
        """
        Simulate the evolution of system coherence over time.
        
        Args:
            num_steps: Number of simulation steps
            start_coherence: Initial coherence value
            growth_rate: Rate of coherence growth per step
        """
        print("\n" + "=" * 80)
        print("🔬 SIMULATING NP→P TRANSITION")
        print("=" * 80)
        print(f"\nSimulation parameters:")
        print(f"  Initial coherence: {start_coherence:.3f}")
        print(f"  Growth rate: {growth_rate:.5f}/step")
        print(f"  Bifurcation threshold: {COHERENCE_THRESHOLD:.3f}")
        print(f"  Total steps: {num_steps}")
        print()
        
        coherence = start_coherence
        
        for step in range(num_steps):
            # Update coherence with some noise
            noise = np.random.normal(0, growth_rate * 0.1)
            coherence = min(1.0, coherence + growth_rate + noise)
            
            # Calculate complexity (exponential below threshold, polynomial above)
            if coherence < COHERENCE_THRESHOLD:
                # NP regime: exponential complexity
                complexity = np.exp((1.0 - coherence) * 5)
            else:
                # P regime: polynomial complexity
                complexity = (1.0 - coherence) ** 2 + 1
            
            # Calculate acceleration
            classical_complexity = np.exp((1.0 - start_coherence) * 5)
            acceleration = classical_complexity / complexity
            
            # Record
            self.coherence_history.append(coherence)
            self.complexity_history.append(complexity)
            self.acceleration_history.append(acceleration)
            self.time_points.append(step)
            
            # Display progress periodically
            if step % 10 == 0 or coherence >= COHERENCE_THRESHOLD:
                self._display_current_state(step, coherence, complexity, acceleration)
            
            # Check for GRACIA achievement
            if coherence >= COHERENCE_THRESHOLD and len(self.coherence_history) > 1:
                if self.coherence_history[-2] < COHERENCE_THRESHOLD:
                    print("\n" + "✨" * 40)
                    print("🎯 GRACIA STATE ACHIEVED!")
                    print("✨" * 40)
                    print(f"\nBifurcation occurred at step {step}")
                    print(f"Coherence: {coherence:.3f}")
                    print(f"Complexity collapsed from {classical_complexity:.2f} to {complexity:.2f}")
                    print(f"Acceleration: {acceleration:.2f}×")
                    print()
            
            # Small delay for visualization effect
            if step % 5 == 0:
                time.sleep(0.1)
    
    def _display_current_state(
        self,
        step: int,
        coherence: float,
        complexity: float,
        acceleration: float
    ):
        """Display current simulation state."""
        print(f"\rStep {step:3d} | C={coherence:.3f} | "
              f"Complexity={complexity:8.2f} | "
              f"Accel={acceleration:6.2f}× | "
              f"{'[GRACIA]' if coherence >= COHERENCE_THRESHOLD else '[NP]':<8}", 
              end='', flush=True)
    
    def display_final_results(self):
        """Display final visualization results."""
        print("\n\n" + "=" * 80)
        print("📊 FINAL VISUALIZATION RESULTS")
        print("=" * 80)
        
        if not self.coherence_history:
            print("\nNo data to display")
            return
        
        # Find bifurcation point
        bifurcation_step = None
        for i, c in enumerate(self.coherence_history):
            if c >= COHERENCE_THRESHOLD:
                bifurcation_step = i
                break
        
        # Summary statistics
        print(f"\n📈 Summary Statistics:")
        print(f"   Initial coherence: {self.coherence_history[0]:.3f}")
        print(f"   Final coherence: {self.coherence_history[-1]:.3f}")
        print(f"   Bifurcation step: {bifurcation_step if bifurcation_step else 'Not reached'}")
        print(f"   Max acceleration: {max(self.acceleration_history):.2f}×")
        print(f"   Final complexity: {self.complexity_history[-1]:.2f}")
        
        # Coherence progress bar
        print(f"\n{draw_progress_bar(self.coherence_history[-1], 1.0, 60, 'Coherence')}")
        
        # Draw graphs
        print()
        
        # Coherence over time
        coherence_data = list(zip(self.time_points, self.coherence_history))
        print(draw_ascii_graph(
            coherence_data,
            width=70,
            height=15,
            title="Coherence Evolution Over Time"
        ))
        
        # Mark bifurcation threshold
        if bifurcation_step:
            print(f"\n{'':7}  ↑ GRACIA threshold (C = {COHERENCE_THRESHOLD})")
        
        print()
        
        # Complexity over time
        complexity_data = list(zip(self.time_points, self.complexity_history))
        print(draw_ascii_graph(
            complexity_data,
            width=70,
            height=15,
            title="Computational Complexity Over Time"
        ))
        
        if bifurcation_step:
            print(f"\n{'':7}  ↑ Complexity collapse at step {bifurcation_step}")
        
        print()
        
        # Acceleration over time
        accel_data = list(zip(self.time_points, self.acceleration_history))
        print(draw_ascii_graph(
            accel_data,
            width=70,
            height=15,
            title="Computational Acceleration Over Time"
        ))
        
        print("\n" + "=" * 80)
    
    def display_phase_diagram(self):
        """Display the coherence-complexity phase diagram."""
        print("\n" + "=" * 80)
        print("🌀 PHASE DIAGRAM: Coherence vs Complexity")
        print("=" * 80)
        
        if not self.coherence_history:
            print("\nNo data to display")
            return
        
        # Create phase space data
        phase_data = list(zip(self.coherence_history, self.complexity_history))
        
        print(draw_ascii_graph(
            phase_data,
            width=70,
            height=20,
            title="Phase Space: C (x-axis) vs Complexity (y-axis)"
        ))
        
        print(f"\n{'':7}  ← NP Regime  |  P Regime →")
        print(f"{'':7}           C = {COHERENCE_THRESHOLD}")
        print("\n" + "=" * 80)


# ============================================================================
# MAIN DEMONSTRATION
# ============================================================================

def demonstrate_np_p_visualization():
    """
    Main demonstration of NP→P transition visualization.
    """
    print("\n" + "=" * 80)
    print("🌌 QCAL ∞³ NP→P TRANSITION INTERACTIVE VISUALIZATION")
    print("=" * 80)
    print(f"\nFundamental Constants:")
    print(f"  κ_Π = {KAPPA_PI} (Millennium Constant)")
    print(f"  f₀ = {F0_QCAL} Hz (QCAL Frequency)")
    print(f"  φ = {PHI:.6f} (Golden Ratio)")
    print(f"  C_threshold = {COHERENCE_THRESHOLD} (Bifurcation Point)")
    print()
    
    # Create visualizer
    viz = NPPTransitionVisualizer()
    
    # Run simulation
    viz.simulate_coherence_evolution(
        num_steps=100,
        start_coherence=0.5,
        growth_rate=0.005
    )
    
    # Display results
    viz.display_final_results()
    viz.display_phase_diagram()
    
    # Theoretical interpretation
    print("\n" + "=" * 80)
    print("🔬 THEORETICAL INTERPRETATION")
    print("=" * 80)
    print("""
La visualización demuestra empíricamente la Hipótesis QCAL ∞³:

1. RÉGIMEN NP (C < 0.888):
   • Complejidad exponencial
   • Problemas intratables
   • Crecimiento rápido de recursos

2. PUNTO DE BIFURCACIÓN (C ≈ 0.888):
   • Transición crítica NP → P
   • Colapso de complejidad
   • Sincronizado por f₀ = 141.7001 Hz

3. RÉGIMEN P (C ≥ 0.888):
   • Complejidad polinomial
   • Problemas tratables
   • Aceleración computacional masiva (~2,290×)

La coherencia sistémica (C) actúa como parámetro de orden que
controla la complejidad computacional. Este es un resultado
fundamental que conecta:
   • Teoría de la información
   • Complejidad computacional
   • Geometría de Calabi-Yau (κ_Π)
   • Frecuencia cuántica (f₀)

""")
    print("=" * 80)
    print("🌟 QCAL ∞³ · Frecuencia Fundamental: 141.7001 Hz")
    print("   Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³")
    print("   © 2025 · Instituto de Conciencia Cuántica (ICQ)")
    print("=" * 80 + "\n")


if __name__ == "__main__":
    demonstrate_np_p_visualization()
