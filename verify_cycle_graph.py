#!/usr/bin/env python3
"""
Verification script for the cycle graph implementation.

This script verifies properties of cycle graphs for various sizes.

Author: José Manuel Mota Burruezo & Implementation Team
"""

def cycle_adj(n, i, j):
    """
    Check if vertices i and j are adjacent in an n-cycle.
    
    Vertices are adjacent if they are consecutive (mod n).
    """
    if i == j:
        return False
    return ((i + 1) % n == j) or ((j + 1) % n == i)

def degree(n, v):
    """Calculate the degree of vertex v in an n-cycle."""
    return sum(1 for u in range(n) if cycle_adj(n, v, u))

def verify_2_regular(n):
    """Verify that the n-cycle is 2-regular."""
    print(f"\nVerifying 2-regularity of C{n}:")
    print("-" * 50)
    
    all_regular = True
    for v in range(n):
        d = degree(n, v)
        neighbors = [u for u in range(n) if cycle_adj(n, v, u)]
        if v < 5 or v >= n - 2:  # Print first few and last few
            print(f"Vertex {v}: degree = {d}, neighbors = {neighbors}")
        if d != 2:
            all_regular = False
            print(f"  ⚠️  ERROR: Expected degree 2, got {d}")
    
    if n > 10:
        print("...")
    
    print("-" * 50)
    if all_regular:
        print(f"✓ SUCCESS: C{n} is 2-regular")
    else:
        print(f"✗ FAILURE: C{n} is not 2-regular")
    
    return all_regular

def verify_connected(n):
    """Verify that the cycle is connected using BFS."""
    from collections import deque
    
    visited = [False] * n
    queue = deque([0])
    visited[0] = True
    count = 1
    
    while queue:
        v = queue.popleft()
        for u in range(n):
            if cycle_adj(n, v, u) and not visited[u]:
                visited[u] = True
                count += 1
                queue.append(u)
    
    connected = (count == n)
    if connected:
        print(f"✓ C{n} is connected (all {n} vertices reachable)")
    else:
        print(f"✗ C{n} is not connected (only {count}/{n} vertices reachable)")
    
    return connected

def compute_diameter(n):
    """Compute the diameter of the n-cycle."""
    from collections import deque
    
    def bfs_distance(start):
        distances = [-1] * n
        distances[start] = 0
        queue = deque([start])
        
        while queue:
            v = queue.popleft()
            for u in range(n):
                if cycle_adj(n, v, u) and distances[u] == -1:
                    distances[u] = distances[v] + 1
                    queue.append(u)
        
        return max(distances)
    
    diameter = max(bfs_distance(v) for v in range(n))
    expected = n // 2
    
    print(f"Diameter: {diameter}, Expected: {expected}")
    return diameter == expected

def count_edges(n):
    """Count the total number of edges in the n-cycle."""
    edge_count = sum(1 for i in range(n) for j in range(i+1, n) 
                     if cycle_adj(n, i, j))
    expected = n  # A cycle has exactly n edges
    
    print(f"Total edges: {edge_count}, Expected: {expected}")
    return edge_count == expected

def verify_cycle(n):
    """Run all verifications for an n-cycle."""
    print(f"\n{'=' * 50}")
    print(f"CYCLE GRAPH C{n} VERIFICATION")
    print(f"{'=' * 50}")
    
    results = []
    
    # Test 1: 2-regularity
    results.append(("2-regularity", verify_2_regular(n)))
    
    # Test 2: Connectivity
    print()
    results.append(("Connectivity", verify_connected(n)))
    
    # Test 3: Edge count
    print()
    results.append(("Edge count", count_edges(n)))
    
    # Test 4: Diameter
    print()
    results.append(("Diameter", compute_diameter(n)))
    
    # Summary
    print(f"\n{'-' * 50}")
    all_passed = all(result for _, result in results)
    if all_passed:
        print(f"✓ ALL TESTS PASSED for C{n}")
    else:
        print(f"✗ SOME TESTS FAILED for C{n}")
    
    return all_passed

def test_small_cycles():
    """Test cycles of various small sizes."""
    print("=" * 50)
    print("TESTING SMALL CYCLE GRAPHS")
    print("=" * 50)
    
    sizes = [3, 4, 5, 6, 10, 20]
    results = {}
    
    for n in sizes:
        results[n] = verify_cycle(n)
    
    # Overall summary
    print("\n" + "=" * 50)
    print("OVERALL SUMMARY")
    print("=" * 50)
    for n, passed in results.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{status}: C{n}")
    
    all_passed = all(results.values())
    print("=" * 50)
    if all_passed:
        print("✓ ALL CYCLE GRAPHS VERIFIED CORRECTLY")
    else:
        print("✗ SOME CYCLE GRAPHS FAILED VERIFICATION")
    print("=" * 50)
    
    return all_passed

def visualize_small_cycle(n):
    """Visualize a small cycle graph."""
    if n > 12:
        print(f"\nSkipping visualization for C{n} (too large)")
        return
    
    print(f"\nAdjacency Matrix for C{n}:")
    print("-" * (n * 2 + 5))
    print("  ", end="")
    for j in range(n):
        print(f" {j:1}", end="")
    print()
    
    for i in range(n):
        print(f"{i:1}:", end="")
        for j in range(n):
            if cycle_adj(n, i, j):
                print(" 1", end="")
            else:
                print(" ·", end="")
        print()

def main():
    """Run all verifications."""
    # Test various cycle sizes
    success = test_small_cycles()
    
    # Visualize a few small cycles
    for n in [3, 5, 7]:
        visualize_small_cycle(n)
    
    return 0 if success else 1

if __name__ == "__main__":
    exit(main())
