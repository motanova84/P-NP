#!/usr/bin/env python3
"""
Verification script for the Petersen graph implementation.

This script verifies the properties of the Petersen graph that we've
implemented in Lean, serving as a computational check.

Author: José Manuel Mota Burruezo & Implementation Team
"""

def petersen_adj(i, j):
    """
    Check if vertices i and j are adjacent in the Petersen graph.
    
    Structure:
    - Outer pentagon: 0-1-2-3-4-0
    - Inner star: 5-7-9-6-8-5 (distance 2 connections)
    - Spokes: 0-5, 1-6, 2-7, 3-8, 4-9
    """
    if i == j:
        return False
    
    # Outer pentagon (vertices 0-4)
    if i < 5 and j < 5:
        return ((i + 1) % 5 == j % 5) or ((j + 1) % 5 == i % 5)
    
    # Inner star (vertices 5-9, connecting at distance 2)
    if i >= 5 and j >= 5:
        ii = i - 5
        jj = j - 5
        return ((ii + 2) % 5 == jj) or ((jj + 2) % 5 == ii)
    
    # Spoke connections
    if i < 5 and j >= 5:
        return j == i + 5
    if j < 5 and i >= 5:
        return i == j + 5
    
    return False

def degree(v):
    """Calculate the degree of vertex v."""
    return sum(1 for u in range(10) if petersen_adj(v, u))

def verify_3_regular():
    """Verify that the Petersen graph is 3-regular."""
    print("Verifying 3-regularity of Petersen graph:")
    print("-" * 50)
    
    all_regular = True
    for v in range(10):
        d = degree(v)
        neighbors = [u for u in range(10) if petersen_adj(v, u)]
        print(f"Vertex {v}: degree = {d}, neighbors = {neighbors}")
        if d != 3:
            all_regular = False
            print(f"  ⚠️  ERROR: Expected degree 3, got {d}")
    
    print("-" * 50)
    if all_regular:
        print("✓ SUCCESS: All vertices have degree 3")
        print("✓ The Petersen graph is 3-regular")
    else:
        print("✗ FAILURE: Not all vertices have degree 3")
    
    return all_regular

def verify_symmetry():
    """Verify that the adjacency relation is symmetric."""
    print("\nVerifying symmetry of adjacency relation:")
    print("-" * 50)
    
    symmetric = True
    for i in range(10):
        for j in range(10):
            if petersen_adj(i, j) != petersen_adj(j, i):
                print(f"✗ Asymmetry found: adj({i},{j}) = {petersen_adj(i,j)}, "
                      f"adj({j},{i}) = {petersen_adj(j,i)}")
                symmetric = False
    
    if symmetric:
        print("✓ SUCCESS: Adjacency relation is symmetric")
    else:
        print("✗ FAILURE: Adjacency relation is not symmetric")
    
    return symmetric

def count_edges():
    """Count the total number of edges."""
    edge_count = sum(1 for i in range(10) for j in range(i+1, 10) 
                     if petersen_adj(i, j))
    print(f"\nTotal edges: {edge_count}")
    print(f"Expected for 3-regular graph on 10 vertices: {3 * 10 // 2} = 15")
    return edge_count == 15

def verify_no_loops():
    """Verify that there are no self-loops."""
    print("\nVerifying no self-loops:")
    print("-" * 50)
    
    no_loops = True
    for v in range(10):
        if petersen_adj(v, v):
            print(f"✗ Self-loop found at vertex {v}")
            no_loops = False
    
    if no_loops:
        print("✓ SUCCESS: No self-loops found")
    else:
        print("✗ FAILURE: Self-loops detected")
    
    return no_loops

def compute_diameter():
    """Compute the diameter of the Petersen graph using BFS."""
    from collections import deque
    
    def bfs_distance(start):
        """BFS to find distances from start vertex."""
        distances = [-1] * 10
        distances[start] = 0
        queue = deque([start])
        
        while queue:
            v = queue.popleft()
            for u in range(10):
                if petersen_adj(v, u) and distances[u] == -1:
                    distances[u] = distances[v] + 1
                    queue.append(u)
        
        return distances
    
    max_distance = 0
    for v in range(10):
        distances = bfs_distance(v)
        max_dist = max(distances)
        max_distance = max(max_distance, max_dist)
    
    print(f"\nDiameter: {max_distance}")
    print(f"Expected: 2 (Petersen graph has diameter 2)")
    return max_distance == 2

def visualize_graph():
    """Print adjacency matrix for visualization."""
    print("\nAdjacency Matrix:")
    print("-" * 50)
    print("  ", end="")
    for j in range(10):
        print(f" {j}", end="")
    print()
    
    for i in range(10):
        print(f"{i}:", end="")
        for j in range(10):
            if petersen_adj(i, j):
                print(" 1", end="")
            else:
                print(" ·", end="")
        print()

def main():
    """Run all verification tests."""
    print("=" * 50)
    print("PETERSEN GRAPH VERIFICATION")
    print("=" * 50)
    
    results = []
    
    # Test 1: 3-regularity
    results.append(("3-regularity", verify_3_regular()))
    
    # Test 2: Symmetry
    results.append(("Symmetry", verify_symmetry()))
    
    # Test 3: No self-loops
    results.append(("No self-loops", verify_no_loops()))
    
    # Test 4: Edge count
    results.append(("Edge count", count_edges()))
    
    # Test 5: Diameter
    results.append(("Diameter = 2", compute_diameter()))
    
    # Visualization
    visualize_graph()
    
    # Summary
    print("\n" + "=" * 50)
    print("VERIFICATION SUMMARY")
    print("=" * 50)
    for test_name, passed in results:
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{status}: {test_name}")
    
    all_passed = all(result for _, result in results)
    print("=" * 50)
    if all_passed:
        print("✓ ALL TESTS PASSED")
        print("\nThe Petersen graph implementation is correct!")
    else:
        print("✗ SOME TESTS FAILED")
        print("\nPlease review the implementation.")
    print("=" * 50)
    
    return 0 if all_passed else 1

if __name__ == "__main__":
    exit(main())
