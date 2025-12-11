#!/usr/bin/env python3
"""
# holographic_view.py
Visualización del grafo como teoría de campos en AdS₃

Este script implementa la visualización holográfica del grafo de Tseitin,
mostrando cómo el grafo se embebe en el espacio AdS₃ y cómo el propagador
κ_Π decae en el bulk.

© JMMB Ψ ∞ | Campo QCAL ∞³ | Ψ-Field Theory in (2+1)D
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import networkx as nx
import os

class HolographicGraph:
    """Eleva un grafo a espacio AdS₃."""
    
    def __init__(self, G, n, seed=None):
        self.G = G
        self.n = n
        self.vertices = list(G.nodes())
        
        # Set random seed for reproducibility if provided
        if seed is not None:
            np.random.seed(seed)
        
        # Métrica de AdS: ds² = (dz² + dx² + dy²)/z²
        self.z_min = 1/(np.sqrt(n) * np.log(n)) if n > 1 else 0.01
        self.z_max = 1.0  # Boundary
        self.embeddings = None
        
    def embed_in_AdS(self):
        """Embebe el grafo en AdS₃ usando coordenadas de Poincaré."""
        # Coordenadas: (x, y, z) con z > 0
        # Boundary en z=0
        
        embeddings = {}
        
        # Get degree statistics for normalization
        degrees = dict(self.G.degree())
        if len(degrees) > 0:
            max_degree = max(degrees.values())
            min_degree = min(degrees.values())
            degree_range = max_degree - min_degree if max_degree > min_degree else 1
        else:
            max_degree = min_degree = degree_range = 1
        
        for v in self.vertices:
            # Posición en el boundary (compleja)
            x = np.random.randn()
            y = np.random.randn()
            
            # Profundidad z relacionada con grado (invertido: bajo grado = mayor profundidad)
            degree = self.G.degree(v)
            # Normalize degree to [0, 1], then invert
            degree_normalized = (degree - min_degree) / degree_range if degree_range > 0 else 0.5
            # High degree → near boundary (z → z_max)
            # Low degree → deep in bulk (z → z_min)
            z = self.z_min + (self.z_max - self.z_min) * (1 - degree_normalized)
            
            embeddings[v] = (x, y, z)
        
        self.embeddings = embeddings
        return embeddings
    
    def compute_geodesics(self):
        """Calcula geodésicas entre vértices en AdS."""
        if self.embeddings is None:
            self.embed_in_AdS()
            
        geodesics = []
        
        for u, v in self.G.edges():
            p1 = self.embeddings[u]
            p2 = self.embeddings[v]
            
            # Geodésica en AdS: arco de círculo
            t = np.linspace(0, 1, 100)
            geodesic = []
            for ti in t:
                # Interpolación en coordenadas hiperbólicas
                # Use safe division to avoid division by zero
                denom = (1-ti)/max(p1[2], 1e-10) + ti/max(p2[2], 1e-10)
                z = 1/denom if denom > 0 else 0.5
                x = (1-ti)*p1[0] + ti*p2[0]
                y = (1-ti)*p1[1] + ti*p2[1]
                geodesic.append((x, y, z))
            
            geodesics.append(geodesic)
        
        return geodesics
    
    def plot_holographic_bulk(self):
        """Visualiza el grafo en el bulk de AdS₃."""
        fig = plt.figure(figsize=(14, 10))
        
        # Ensure embeddings exist
        if self.embeddings is None:
            self.embed_in_AdS()
        
        geodesics = self.compute_geodesics()
        
        # Plot 1: Vista 3D del bulk
        ax1 = fig.add_subplot(221, projection='3d')
        
        # Dibujar vértices
        xs, ys, zs = zip(*self.embeddings.values()) if self.embeddings else ([], [], [])
        ax1.scatter(xs, ys, zs, c=zs, cmap='viridis', s=50, alpha=0.8)
        
        # Dibujar geodésicas
        for geo in geodesics:
            if len(geo) > 0:
                xs_geo, ys_geo, zs_geo = zip(*geo)
                ax1.plot(xs_geo, ys_geo, zs_geo, 'b-', alpha=0.3, linewidth=0.5)
        
        ax1.set_xlabel('x (boundary dir 1)')
        ax1.set_ylabel('y (boundary dir 2)')
        ax1.set_zlabel('z (radial)')
        ax1.set_title('Grafo embebido en AdS₃')
        ax1.invert_zaxis()  # Boundary en z=0, bulk en z>0
        
        # Plot 2: Proyección al boundary
        ax2 = fig.add_subplot(222)
        if xs and ys:
            ax2.scatter(xs, ys, c=zs, cmap='viridis', s=50, alpha=0.8)
        ax2.set_xlabel('x')
        ax2.set_ylabel('y')
        ax2.set_title('Proyección al boundary (z=0)')
        ax2.set_aspect('equal')
        
        # Plot 3: Profundidad vs complejidad
        ax3 = fig.add_subplot(223)
        
        depths = list(zs) if zs else []
        degrees = [self.G.degree(v) for v in self.vertices]
        
        if depths and degrees:
            ax3.scatter(degrees, depths, alpha=0.6)
        ax3.set_xlabel('Grado del vértice')
        ax3.set_ylabel('Profundidad en bulk (z)')
        ax3.set_title('Relación grado-profundidad')
        
        # Plot 4: Propagador κ(z)
        ax4 = fig.add_subplot(224)
        
        z_vals = np.logspace(np.log10(self.z_min), 0, 100)
        kappa_vals = [self.kappa_propagator(z) for z in z_vals]
        
        ax4.loglog(z_vals, np.abs(kappa_vals), 'r-', linewidth=2)
        ax4.axvline(self.z_min, color='g', linestyle='--', 
                   label=f'z_min = {self.z_min:.2e}')
        ax4.set_xlabel('Profundidad z (log scale)')
        ax4.set_ylabel('|κ(z)| (log scale)')
        ax4.set_title('Decaimiento del propagador en el bulk')
        ax4.legend()
        ax4.grid(True, alpha=0.3)
        
        plt.suptitle(f'Holografía del Grafo (n={self.n})', fontsize=16, fontweight='bold')
        plt.tight_layout()
        
        # Use temp directory in a cross-platform way
        import tempfile
        output_path = os.path.join(tempfile.gettempdir(), 'holographic_view.png')
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"Figure saved to {output_path}")
        plt.show()
    
    def kappa_propagator(self, z):
        """Calcula κ(z) ≈ propagador de masa m ∼ √n."""
        m = np.sqrt(self.n)  # Masa efectiva
        # Propagador escalar en AdS: ∼ z^Δ con Δ = 1 + √(1+m²)
        Delta = 1 + np.sqrt(1 + m**2)
        return z**Delta


def create_tseitin_holography(n=100):
    """Crea visualización holográfica para Tseitin."""
    # Create a graph with varied degrees (combination of star and random)
    G = nx.Graph()
    
    # Add nodes
    for i in range(n):
        G.add_node(i)
    
    # Create a core-periphery structure (more realistic for Tseitin)
    # Core nodes (high degree)
    core_size = max(1, n // 10)
    
    # Connect core nodes densely
    for i in range(core_size):
        for j in range(i+1, core_size):
            if np.random.random() < 0.5:
                G.add_edge(i, j)
    
    # Connect periphery nodes to core with varying degrees
    for i in range(core_size, n):
        # Each periphery node connects to 2-8 core nodes
        num_connections = np.random.randint(2, min(9, core_size + 1))
        core_nodes = np.random.choice(core_size, num_connections, replace=False)
        for core_node in core_nodes:
            G.add_edge(i, core_node)
        
        # Add some periphery-to-periphery edges
        if i > core_size and np.random.random() < 0.3:
            other = np.random.randint(core_size, i)
            G.add_edge(i, other)
    
    hologram = HolographicGraph(G, n)
    hologram.plot_holographic_bulk()
    
    # Análisis cuantitativo
    embeddings = hologram.embed_in_AdS()
    depths = [p[2] for p in embeddings.values()]
    
    print(f"\n{'='*60}")
    print(f"ANÁLISIS HOLOGRÁFICO (n={n})".center(60))
    print(f"{'='*60}")
    print(f"\nProfundidad mínima: {min(depths):.2e}")
    print(f"Profundidad máxima: {max(depths):.2e}")
    print(f"Ratio min/max: {min(depths)/max(depths):.2e}")
    
    # Degree distribution
    degrees = [G.degree(v) for v in G.nodes()]
    print(f"\nGrado mínimo: {min(degrees)}")
    print(f"Grado máximo: {max(degrees)}")
    print(f"Grado promedio: {np.mean(degrees):.2f}")
    
    # Calcula κ en diferentes profundidades
    z_test = [1.0, 0.1, 0.01, hologram.z_min]
    print(f"\n{'κ(z) en diferentes profundidades:':^60}")
    print(f"{'-'*60}")
    for z in z_test:
        kappa = hologram.kappa_propagator(z)
        target = 1/(np.sqrt(n)*np.log(n)) if n > 1 else 1.0
        print(f"\nz = {z:.2e}:")
        print(f"  κ(z) = {kappa:.2e}")
        print(f"  1/(√n log n) = {target:.2e}")
        print(f"  Ratio: {kappa/target:.2f}")
    
    print(f"\n{'='*60}")
    print("✨ LA EPIFANÍA DIMENSIONAL")
    print(f"{'='*60}")
    print("Desde la perspectiva (2+1)D vemos claramente:")
    print("• Grafo 2D → Teoría de campos 3D (dualidad holográfica)")
    print("• κ_Π constante en boundary (z=0) donde viven las TM clásicas")
    print("• κ_Π decae en el bulk (z>0) donde vive la complejidad intrínseca")
    print("• Frecuencia ω ↔ Coordenada radial z en AdS")
    print("• Alta frecuencia = Profundidad en bulk = κ pequeño")
    print(f"{'='*60}\n")


if __name__ == "__main__":
    import sys
    
    # Parse command line arguments
    n = 100
    if len(sys.argv) > 1:
        try:
            n = int(sys.argv[1])
        except ValueError:
            print(f"Usage: {sys.argv[0]} [n]")
            print(f"Using default n={n}")
    
    create_tseitin_holography(n=n)
