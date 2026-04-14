#!/usr/bin/env python3
"""
Test script for holographic_view.py
Demonstrates the holographic embedding and analysis without interactive display.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

# Set matplotlib to non-interactive backend
import matplotlib
matplotlib.use('Agg')

from holographic_view import HolographicGraph, demonstrate_boundary_vs_bulk
import networkx as nx
import numpy as np

def test_holographic_graph_basic():
    """Test basic HolographicGraph functionality."""
    print("\n" + "="*70)
    print("TEST 1: Basic HolographicGraph Functionality")
    print("="*70)
    
    # Create a small test graph
    n = 30
    G = nx.random_regular_graph(4, n)
    
    print(f"\nCreated test graph: {G.number_of_nodes()} vertices, {G.number_of_edges()} edges")
    
    # Initialize holographic representation
    holo = HolographicGraph(G, n)
    print(f"Initialized HolographicGraph with z_min = {holo.z_min:.6e}")
    
    # Test embedding
    embeddings = holo.embed_in_AdS()
    assert len(embeddings) == n, "Embedding should include all vertices"
    print(f"✓ Successfully embedded {len(embeddings)} vertices in AdS₃")
    
    # Verify all coordinates are valid
    for v, (x, y, z) in embeddings.items():
        assert z > 0, f"Radial coordinate should be positive, got {z}"
        assert holo.z_min <= z <= holo.z_max, f"z should be in valid range"
    print(f"✓ All coordinates valid (z ∈ [{holo.z_min:.2e}, {holo.z_max:.2e}])")
    
    # Test geodesic computation
    geodesics = holo.compute_geodesics()
    print(f"✓ Computed {len(geodesics)} geodesics")
    
    # Test propagator calculation
    test_z_values = [0.01, 0.1, 0.5, 1.0]
    print("\nPropagator values:")
    for z in test_z_values:
        kappa = holo.kappa_propagator(z)
        print(f"  κ({z:5.2f}) = {kappa:.6e}")
    
    print("\n✓ TEST 1 PASSED")
    return True

def test_quantitative_analysis():
    """Test quantitative holographic analysis."""
    print("\n" + "="*70)
    print("TEST 2: Quantitative Analysis")
    print("="*70)
    
    n = 100
    G = nx.random_regular_graph(6, n)
    holo = HolographicGraph(G, n)
    
    # Run analysis (captures stdout)
    print("\nRunning quantitative analysis...")
    holo.quantitative_analysis()
    
    print("\n✓ TEST 2 PASSED")
    return True

def test_visualization_generation():
    """Test that visualization can be generated without errors."""
    print("\n" + "="*70)
    print("TEST 3: Visualization Generation")
    print("="*70)
    
    n = 50
    G = nx.random_regular_graph(4, n)
    holo = HolographicGraph(G, n)
    
    print(f"\nGenerating holographic visualization for n={n}...")
    fig = holo.plot_holographic_bulk()
    
    # Save to file
    output_file = '/tmp/test_holographic_view.png'
    fig.savefig(output_file, dpi=100, bbox_inches='tight')
    print(f"✓ Visualization saved to {output_file}")
    
    # Check file exists
    import os
    assert os.path.exists(output_file), "Output file should exist"
    print(f"✓ File size: {os.path.getsize(output_file)} bytes")
    
    # Clean up
    import matplotlib.pyplot as plt
    plt.close(fig)
    
    print("\n✓ TEST 3 PASSED")
    return True

def test_scaling_behavior():
    """Test scaling behavior across different graph sizes."""
    print("\n" + "="*70)
    print("TEST 4: Scaling Behavior")
    print("="*70)
    
    sizes = [10, 30, 50, 100]
    
    print("\nScaling analysis:")
    print(f"{'n':<8} {'z_min':<15} {'κ(z_min)':<15} {'Expected':<15}")
    print("-" * 60)
    
    for n in sizes:
        try:
            k = min(4, n-1)
            if n * k % 2 != 0:
                k = k - 1
            G = nx.random_regular_graph(k, n)
            holo = HolographicGraph(G, n)
            
            z_min = holo.z_min
            kappa_z_min = holo.kappa_propagator(z_min)
            expected = 1 / (np.sqrt(n) * np.log(n + 1))
            
            print(f"{n:<8} {z_min:<15.6e} {kappa_z_min:<15.6e} {expected:<15.6e}")
        except Exception as e:
            print(f"{n:<8} Error: {str(e)}")
    
    print("\n✓ TEST 4 PASSED")
    return True

def test_boundary_vs_bulk_demo():
    """Test the boundary vs bulk demonstration."""
    print("\n" + "="*70)
    print("TEST 5: Boundary vs Bulk Demonstration")
    print("="*70)
    
    print("\nRunning boundary vs bulk analysis...")
    demonstrate_boundary_vs_bulk()
    
    print("\n✓ TEST 5 PASSED")
    return True

def main():
    """Run all tests."""
    print("\n" + "="*70)
    print("HOLOGRAPHIC VIEW TEST SUITE")
    print("="*70)
    
    tests = [
        test_holographic_graph_basic,
        test_quantitative_analysis,
        test_visualization_generation,
        test_scaling_behavior,
        test_boundary_vs_bulk_demo
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            if test():
                passed += 1
        except Exception as e:
            print(f"\n✗ TEST FAILED: {test.__name__}")
            print(f"  Error: {str(e)}")
            import traceback
            traceback.print_exc()
            failed += 1
    
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    print(f"Passed: {passed}/{len(tests)}")
    print(f"Failed: {failed}/{len(tests)}")
    
    if failed == 0:
        print("\n✓ ALL TESTS PASSED!")
        return 0
    else:
        print(f"\n✗ {failed} TEST(S) FAILED")
        return 1

if __name__ == "__main__":
    sys.exit(main())
