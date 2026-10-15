#!/usr/bin/env python3
"""
Test script to visualize coherence approach vs isolated theorems.
"""

import matplotlib.pyplot as plt
import matplotlib.patches as patches
import numpy as np
from matplotlib.patches import FancyBboxPatch, Circle, FancyArrowPatch
import io
import sys

# Configuration for non-interactive backend
plt.switch_backend('Agg')

def create_comparison_diagram():
    """Create a visual comparison of the two approaches."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))
    
    # Left side: Isolated theorems
    ax1.set_xlim(0, 10)
    ax1.set_ylim(0, 10)
    ax1.set_aspect('equal')
    ax1.axis('off')
    ax1.set_title('TRADICIONAL: Teoremas Aislados\n(Escasez)', 
                  fontsize=16, fontweight='bold', pad=20)
    
    # Draw isolated boxes
    theorems = [
        {'pos': (2, 7), 'text': 'Geometría\nCY', 'color': 'lightblue'},
        {'pos': (8, 7), 'text': 'Información\nIC', 'color': 'lightgreen'},
        {'pos': (2, 3), 'text': 'Computación\nP≠NP', 'color': 'lightcoral'},
        {'pos': (8, 3), 'text': 'Biología\nARN', 'color': 'lightyellow'},
    ]
    
    for thm in theorems:
        box = FancyBboxPatch((thm['pos'][0]-0.8, thm['pos'][1]-0.5), 
                             1.6, 1, 
                             boxstyle="round,pad=0.1", 
                             facecolor=thm['color'], 
                             edgecolor='black', 
                             linewidth=2)
        ax1.add_patch(box)
        ax1.text(thm['pos'][0], thm['pos'][1], thm['text'], 
                ha='center', va='center', fontsize=10, fontweight='bold')
    
    # Add X marks to show disconnection
    ax1.text(5, 7, '✗', fontsize=40, ha='center', va='center', color='red', alpha=0.3)
    ax1.text(5, 3, '✗', fontsize=40, ha='center', va='center', color='red', alpha=0.3)
    ax1.text(2, 5, '✗', fontsize=40, ha='center', va='center', color='red', alpha=0.3)
    ax1.text(8, 5, '✗', fontsize=40, ha='center', va='center', color='red', alpha=0.3)
    
    ax1.text(5, 0.5, 'Sin unificación • Fragmentado • Lento', 
            ha='center', fontsize=11, style='italic', color='red')
    
    # Right side: Coherence-based
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 10)
    ax2.set_aspect('equal')
    ax2.axis('off')
    ax2.set_title('NUEVO: Coherencia Cuántica\n(Abundancia)', 
                  fontsize=16, fontweight='bold', pad=20)
    
    # Draw central coherence source
    center = Circle((5, 5), 0.8, facecolor='gold', edgecolor='orange', linewidth=3)
    ax2.add_patch(center)
    ax2.text(5, 5.5, 'Coherencia', ha='center', va='center', 
            fontsize=11, fontweight='bold')
    ax2.text(5, 4.7, 'Cuántica', ha='center', va='center', 
            fontsize=11, fontweight='bold')
    ax2.text(5, 4.1, 'κ_Π=2.5773', ha='center', va='center', 
            fontsize=9, style='italic')
    
    # Draw connected manifestations
    manifestations = [
        {'pos': (2, 8), 'text': 'Geometría\nCY', 'color': 'lightblue'},
        {'pos': (8, 8), 'text': 'Información\nIC', 'color': 'lightgreen'},
        {'pos': (1.5, 2), 'text': 'Computación\nP≠NP', 'color': 'lightcoral'},
        {'pos': (8.5, 2), 'text': 'Biología\nConsc.', 'color': 'lightyellow'},
    ]
    
    for man in manifestations:
        # Draw arrow from center
        arrow = FancyArrowPatch((5, 5), man['pos'],
                               arrowstyle='->', 
                               connectionstyle="arc3,rad=0.1",
                               color='orange', 
                               linewidth=2.5,
                               mutation_scale=20)
        ax2.add_patch(arrow)
        
        # Draw manifestation box
        box = FancyBboxPatch((man['pos'][0]-0.8, man['pos'][1]-0.5), 
                             1.6, 1, 
                             boxstyle="round,pad=0.1", 
                             facecolor=man['color'], 
                             edgecolor='orange', 
                             linewidth=2)
        ax2.add_patch(box)
        ax2.text(man['pos'][0], man['pos'][1], man['text'], 
                ha='center', va='center', fontsize=10, fontweight='bold')
    
    ax2.text(5, 0.5, 'Unificado • Conectado • Rápido', 
            ha='center', fontsize=11, style='italic', color='green')
    
    plt.tight_layout()
    return fig

if __name__ == "__main__":
    print("Generando visualización de coherencia cuántica vs teoremas aislados...")
    fig = create_comparison_diagram()
    
    # Save to file
    output_file = 'coherencia_vs_aislados.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"✅ Visualización guardada en: {output_file}")
    print("\nLa imagen muestra:")
    print("  IZQUIERDA: Teoremas aislados sin conexión (✗)")
    print("  DERECHA: Coherencia cuántica unifica todo (→)")
    plt.close()
