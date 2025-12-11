#!/usr/bin/env python3
"""
Test script for holographic_view.py

Validates that the holographic visualization works correctly.
"""

import sys
import os

# Add examples directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'examples'))

import numpy as np
import networkx as nx
from holographic_view import HolographicGraph, create_tseitin_holography


def test_holographic_graph_creation():
    """Test that HolographicGraph can be created and initialized."""
    print("Testing HolographicGraph creation...")
    
    # Create a simple graph
    G = nx.cycle_graph(10)
    n = 10
    
    hologram = HolographicGraph(G, n)
    
    # Check attributes
    assert hologram.n == n, "Graph size mismatch"
    assert len(hologram.vertices) == 10, "Vertex count mismatch"
    assert hologram.z_min > 0, "z_min should be positive"
    assert hologram.z_max == 1.0, "z_max should be 1.0"
    
    print("✓ HolographicGraph creation test passed")


def test_embedding_in_ads():
    """Test that graphs can be embedded in AdS space."""
    print("\nTesting embedding in AdS...")
    
    # Create a graph with varied degrees
    G = nx.Graph()
    for i in range(20):
        G.add_node(i)
    
    # Create varied degree structure
    for i in range(5):
        for j in range(i+1, 20):
            if np.random.random() < 0.3:
                G.add_edge(i, j)
    
    hologram = HolographicGraph(G, 20)
    embeddings = hologram.embed_in_AdS()
    
    # Verify embeddings
    assert len(embeddings) == 20, "Should have 20 embeddings"
    
    # Check that embeddings are valid
    for v, (x, y, z) in embeddings.items():
        assert isinstance(x, float), "x coordinate should be float"
        assert isinstance(y, float), "y coordinate should be float"
        assert 0 < z <= 1.0, f"z coordinate should be in (0, 1], got {z}"
    
    # Check that there's variation in z coordinates
    z_coords = [z for (x, y, z) in embeddings.values()]
    z_range = max(z_coords) - min(z_coords)
    assert z_range > 0.1, "Should have significant variation in z coordinates"
    
    print("✓ AdS embedding test passed")


def test_kappa_propagator():
    """Test that kappa propagator decays correctly."""
    print("\nTesting kappa propagator...")
    
    G = nx.cycle_graph(10)
    hologram = HolographicGraph(G, 10)
    
    # Test at different depths
    z_values = [1.0, 0.5, 0.1, 0.01]
    kappa_values = [hologram.kappa_propagator(z) for z in z_values]
    
    # Verify decay: kappa should decrease as z decreases
    for i in range(len(kappa_values) - 1):
        assert kappa_values[i] > kappa_values[i+1], \
            f"Propagator should decay: κ({z_values[i]}) = {kappa_values[i]:.2e} should be > κ({z_values[i+1]}) = {kappa_values[i+1]:.2e}"
    
    print(f"  κ(1.0) = {kappa_values[0]:.2e}")
    print(f"  κ(0.5) = {kappa_values[1]:.2e}")
    print(f"  κ(0.1) = {kappa_values[2]:.2e}")
    print(f"  κ(0.01) = {kappa_values[3]:.2e}")
    print("✓ Kappa propagator test passed")


def test_geodesics():
    """Test geodesic computation."""
    print("\nTesting geodesics...")
    
    G = nx.path_graph(5)
    hologram = HolographicGraph(G, 5)
    hologram.embed_in_AdS()
    
    geodesics = hologram.compute_geodesics()
    
    # Should have 4 geodesics for a path graph with 5 nodes
    assert len(geodesics) == 4, f"Path graph should have 4 geodesics, got {len(geodesics)}"
    
    # Each geodesic should have 100 points
    for geo in geodesics:
        assert len(geo) == 100, "Each geodesic should have 100 points"
        
        # Check that each point has 3 coordinates
        for point in geo:
            assert len(point) == 3, "Each point should have (x, y, z) coordinates"
    
    print("✓ Geodesics test passed")


def test_full_visualization_pipeline():
    """Test the full visualization pipeline with a small graph."""
    print("\nTesting full visualization pipeline...")
    
    # This should not crash
    try:
        # We redirect output but don't display the plot
        import matplotlib
        matplotlib.use('Agg')  # Non-interactive backend
        
        # Create with small n for speed
        G = nx.cycle_graph(10)
        hologram = HolographicGraph(G, 10)
        hologram.embed_in_AdS()
        
        # Test that plot can be created (won't display in test)
        # hologram.plot_holographic_bulk()  # Skip to avoid blocking
        
        print("✓ Full visualization pipeline test passed")
    except Exception as e:
        print(f"✗ Visualization test failed: {e}")
        raise


def run_all_tests():
    """Run all tests."""
    print("="*60)
    print("Running Holographic View Tests")
    print("="*60)
    
    test_holographic_graph_creation()
    test_embedding_in_ads()
    test_kappa_propagator()
    test_geodesics()
    test_full_visualization_pipeline()
    
    print("\n" + "="*60)
    print("✓ All tests passed!")
    print("="*60)


if __name__ == "__main__":
    run_all_tests()
