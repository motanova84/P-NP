"""
Test Suite for Vortex Quantum Bridge Module
============================================

Comprehensive tests for wormhole engineering and quantum transport.

Tests:
- VortexQuantumBridge initialization
- Spacetime metric g_rr calculation
- Quantum jump probability (84.63% at core)
- Inter-repository transport protocol (34 nodes)
- Wormhole stability
- Viscosity tensor

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from vortex_quantum_bridge import (
    VortexQuantumBridge,
    VortexType,
    QuantumNode,
    WormholeMetrics,
    demonstrate_vortex_bridge
)


class TestVortexQuantumBridgeInitialization:
    """Test initialization of VortexQuantumBridge."""
    
    def test_default_initialization(self):
        """Test default initialization parameters."""
        bridge = VortexQuantumBridge()
        
        assert bridge.f0 == 141.7001
        assert bridge.tau0 == pytest.approx(1.0 / 141.7001)
        assert bridge.num_nodes == 34
        assert bridge.vortex_type == VortexType.SINGULAR
        assert bridge.kappa_pi == pytest.approx(2.5773302292)
        assert bridge.core_probability == pytest.approx(0.8463)
    
    def test_custom_parameters(self):
        """Test initialization with custom parameters."""
        bridge = VortexQuantumBridge(
            f0=100.0,
            num_nodes=50,
            vortex_type=VortexType.RANKINE
        )
        
        assert bridge.f0 == 100.0
        assert bridge.num_nodes == 50
        assert bridge.vortex_type == VortexType.RANKINE
        assert len(bridge.nodes) == 50
    
    def test_network_initialization(self):
        """Test that transport network is initialized."""
        bridge = VortexQuantumBridge(num_nodes=34)
        
        assert len(bridge.nodes) == 34
        
        # Check nodes have correct attributes
        for node in bridge.nodes:
            assert isinstance(node, QuantumNode)
            assert node.coherence > 0.0
            assert node.energy > 0.0
            assert len(node.position) == 3


class TestMetricCalculation:
    """Test spacetime metric g_rr calculation."""
    
    def test_metric_at_core(self):
        """Test g_rr = 0 at core (r ≤ r_core)."""
        bridge = VortexQuantumBridge()
        
        g_rr = bridge.calculate_metric_grr(r=0.0)
        assert g_rr == 0.0
        
        g_rr = bridge.calculate_metric_grr(r=bridge.r_core)
        assert g_rr == 0.0
    
    def test_metric_outside_core(self):
        """Test g_rr > 0 outside core."""
        bridge = VortexQuantumBridge()
        
        g_rr = bridge.calculate_metric_grr(r=2.0 * bridge.r_core)
        assert g_rr > 0.0
        
        g_rr = bridge.calculate_metric_grr(r=10.0 * bridge.r_core)
        assert g_rr > 0.0
    
    def test_metric_approaches_one(self):
        """Test g_rr → 1 as r → ∞."""
        bridge = VortexQuantumBridge()
        
        g_rr = bridge.calculate_metric_grr(r=100.0 * bridge.r_core)
        assert g_rr > 0.99
        
        g_rr = bridge.calculate_metric_grr(r=1000.0 * bridge.r_core)
        assert g_rr > 0.999


class TestJumpProbability:
    """Test quantum jump probability calculation."""
    
    def test_probability_at_core(self):
        """Test P(r→0) = 84.63%."""
        bridge = VortexQuantumBridge()
        
        P = bridge.calculate_jump_probability(r=0.0)
        assert P == pytest.approx(0.8463, rel=0.01)
    
    def test_probability_decreases_with_radius(self):
        """Test that probability decreases with distance."""
        bridge = VortexQuantumBridge()
        
        P0 = bridge.calculate_jump_probability(r=0.0)
        P1 = bridge.calculate_jump_probability(r=bridge.r_core)
        P2 = bridge.calculate_jump_probability(r=2.0 * bridge.r_core)
        
        assert P0 > P1 > P2
    
    def test_probability_bounds(self):
        """Test that probability is in [0, 1]."""
        bridge = VortexQuantumBridge()
        
        test_radii = [0.0, 0.5, 1.0, 2.0, 5.0, 10.0]
        
        for r in test_radii:
            P = bridge.calculate_jump_probability(r)
            assert 0.0 <= P <= 1.0


class TestCurvatureCalculation:
    """Test spacetime curvature calculation."""
    
    def test_infinite_curvature_at_core(self):
        """Test R → ∞ at singularity."""
        bridge = VortexQuantumBridge()
        
        R = bridge.calculate_curvature(r=0.0)
        assert np.isinf(R)
    
    def test_curvature_decreases_with_radius(self):
        """Test that curvature decreases with distance."""
        bridge = VortexQuantumBridge()
        
        R1 = bridge.calculate_curvature(r=1.5 * bridge.r_core)
        R2 = bridge.calculate_curvature(r=3.0 * bridge.r_core)
        R3 = bridge.calculate_curvature(r=10.0 * bridge.r_core)
        
        assert R1 > R2 > R3


class TestWormholeStability:
    """Test wormhole stability calculation."""
    
    def test_high_stability_at_core(self):
        """Test high stability near core with high coherence."""
        bridge = VortexQuantumBridge()
        
        S = bridge.calculate_wormhole_stability(r=0.1, coherence=0.99)
        assert S > 0.8
    
    def test_low_stability_far_from_core(self):
        """Test low stability far from core."""
        bridge = VortexQuantumBridge()
        
        S = bridge.calculate_wormhole_stability(r=10.0, coherence=0.99)
        assert S < 0.2
    
    def test_stability_depends_on_coherence(self):
        """Test that stability increases with coherence."""
        bridge = VortexQuantumBridge()
        
        S_low = bridge.calculate_wormhole_stability(r=0.5, coherence=0.5)
        S_high = bridge.calculate_wormhole_stability(r=0.5, coherence=0.99)
        
        assert S_high > S_low


class TestWormholeMetrics:
    """Test complete wormhole metrics computation."""
    
    def test_metrics_at_core(self):
        """Test metrics at core."""
        bridge = VortexQuantumBridge()
        
        metrics = bridge.compute_wormhole_metrics(r=0.0, coherence=0.99)
        
        assert isinstance(metrics, WormholeMetrics)
        assert metrics.g_rr == 0.0
        assert metrics.jump_probability == pytest.approx(0.8463, rel=0.01)
        assert metrics.coherence == 0.99
        assert np.isinf(metrics.curvature)
    
    def test_metrics_outside_core(self):
        """Test metrics outside core."""
        bridge = VortexQuantumBridge()
        
        metrics = bridge.compute_wormhole_metrics(r=2.0, coherence=0.99)
        
        assert metrics.g_rr > 0.0
        assert 0.0 < metrics.jump_probability < 1.0
        assert not np.isinf(metrics.curvature)
        assert 0.0 <= metrics.stability <= 1.0


class TestOptimalTransportRadius:
    """Test finding optimal transport radius."""
    
    def test_optimal_radius_found(self):
        """Test that optimal radius is found."""
        bridge = VortexQuantumBridge()
        
        r_opt = bridge.find_optimal_transport_radius(
            min_probability=0.80,
            min_stability=0.90
        )
        
        assert r_opt >= 0.0
        assert r_opt <= 3.0 * bridge.r_core
    
    def test_optimal_radius_near_core(self):
        """Test that optimal radius is close to core."""
        bridge = VortexQuantumBridge()
        
        r_opt = bridge.find_optimal_transport_radius(
            min_probability=0.80,
            min_stability=0.85
        )
        
        # Should be within a few core radii
        assert r_opt < 2.0 * bridge.r_core


class TestNodeConnection:
    """Test node connection through vortex."""
    
    def test_connect_nodes(self):
        """Test connecting nodes to vortex bridge."""
        bridge = VortexQuantumBridge(num_nodes=34)
        
        connected = bridge.connect_nodes(coherence_threshold=0.95)
        
        # Should connect most nodes
        assert connected > 0
        assert connected <= bridge.num_nodes
    
    def test_high_threshold_fewer_connections(self):
        """Test that higher threshold leads to fewer connections."""
        bridge1 = VortexQuantumBridge(num_nodes=34)
        bridge2 = VortexQuantumBridge(num_nodes=34)
        
        # Set same random seed for reproducibility
        np.random.seed(42)
        connected_low = bridge1.connect_nodes(coherence_threshold=0.90)
        
        np.random.seed(42)
        connected_high = bridge2.connect_nodes(coherence_threshold=0.99)
        
        # Lower threshold should connect more nodes (or equal)
        assert connected_low >= connected_high


class TestQuantumTransport:
    """Test quantum transport between nodes."""
    
    def test_transport_requires_connection(self):
        """Test that transport requires both nodes connected."""
        bridge = VortexQuantumBridge(num_nodes=34)
        
        # Don't connect nodes
        result = bridge.execute_quantum_transport(0, 10)
        
        # Should fail if nodes not connected
        if not (bridge.nodes[0].connected and bridge.nodes[10].connected):
            assert result['success'] == False
    
    def test_transport_result_structure(self):
        """Test that transport result has correct structure."""
        bridge = VortexQuantumBridge(num_nodes=34)
        bridge.connect_nodes(coherence_threshold=0.95)
        
        result = bridge.execute_quantum_transport(0, 10)
        
        assert 'success' in result
        assert 'source_id' in result
        assert 'target_id' in result
        assert 'probability' in result
        assert 'coherence' in result
    
    def test_transport_probability_valid(self):
        """Test that transport probability is valid."""
        bridge = VortexQuantumBridge(num_nodes=34)
        bridge.connect_nodes(coherence_threshold=0.90)
        
        result = bridge.execute_quantum_transport(0, 10)
        
        if 'probability' in result:
            assert 0.0 <= result['probability'] <= 1.0


class TestVortexFieldGeneration:
    """Test vortex velocity field generation."""
    
    def test_field_generation(self):
        """Test that vortex field is generated correctly."""
        bridge = VortexQuantumBridge()
        
        # Create grid
        x = np.array([0.0, 1.0, 0.0])
        y = np.array([0.0, 0.0, 1.0])
        z = np.array([0.0, 0.0, 0.0])
        
        v_x, v_y, v_z = bridge.generate_vortex_field(x, y, z)
        
        # Check dimensions
        assert len(v_x) == len(x)
        assert len(v_y) == len(y)
        assert len(v_z) == len(z)
        
        # z-component should be zero for vortex in xy-plane
        assert np.allclose(v_z, 0.0)


class TestViscosityTensor:
    """Test viscosity tensor calculation."""
    
    def test_tensor_dimensions(self):
        """Test that viscosity tensor is 3x3."""
        bridge = VortexQuantumBridge()
        
        position = np.array([1.0, 0.0, 0.0])
        eta_tensor = bridge.calculate_viscosity_tensor(position, coherence=0.99)
        
        assert eta_tensor.shape == (3, 3)
    
    def test_low_viscosity_high_coherence(self):
        """Test low viscosity with high coherence."""
        bridge = VortexQuantumBridge()
        
        position = np.array([1.0, 0.0, 0.0])
        eta_high = bridge.calculate_viscosity_tensor(position, coherence=0.99)
        
        # Should have low viscosity
        assert np.max(eta_high) < 0.1
    
    def test_high_viscosity_low_coherence(self):
        """Test high viscosity with low coherence."""
        bridge = VortexQuantumBridge()
        
        position = np.array([1.0, 0.0, 0.0])
        eta_low = bridge.calculate_viscosity_tensor(position, coherence=0.5)
        
        # Should have higher viscosity
        assert np.max(eta_low) > 0.3


class TestNetworkStatus:
    """Test network status reporting."""
    
    def test_status_structure(self):
        """Test that status has correct structure."""
        bridge = VortexQuantumBridge(num_nodes=34)
        bridge.connect_nodes(coherence_threshold=0.95)
        
        status = bridge.get_network_status()
        
        assert 'total_nodes' in status
        assert 'connected_nodes' in status
        assert 'connection_rate' in status
        assert 'mean_coherence' in status
        assert 'mean_energy' in status
        assert 'vortex_type' in status
        assert 'frequency' in status
    
    def test_status_values(self):
        """Test that status values are valid."""
        bridge = VortexQuantumBridge(num_nodes=34)
        bridge.connect_nodes(coherence_threshold=0.95)
        
        status = bridge.get_network_status()
        
        assert status['total_nodes'] == 34
        assert 0 <= status['connected_nodes'] <= 34
        assert 0.0 <= status['connection_rate'] <= 1.0
        assert status['mean_coherence'] > 0.0
        assert status['mean_energy'] > 0.0


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_full_transport_workflow(self):
        """Test complete quantum transport workflow."""
        # Initialize bridge
        bridge = VortexQuantumBridge(f0=141.7001, num_nodes=34)
        
        # Connect network
        connected = bridge.connect_nodes(coherence_threshold=0.95)
        assert connected > 0
        
        # Get status
        status = bridge.get_network_status()
        assert status['total_nodes'] == 34
        
        # Attempt transport
        if connected >= 2:
            # Find two connected nodes
            connected_nodes = [i for i, n in enumerate(bridge.nodes) if n.connected]
            
            if len(connected_nodes) >= 2:
                result = bridge.execute_quantum_transport(
                    connected_nodes[0],
                    connected_nodes[1]
                )
                
                assert 'success' in result
                assert 'probability' in result
    
    def test_demonstrate_function(self):
        """Test that demonstration function runs without error."""
        try:
            # Redirect output to suppress prints
            import io
            import sys
            old_stdout = sys.stdout
            sys.stdout = io.StringIO()
            
            demonstrate_vortex_bridge()
            
            sys.stdout = old_stdout
            
            success = True
        except Exception as e:
            success = False
        
        assert success == True


class TestVortexTypes:
    """Test different vortex types."""
    
    def test_singular_vortex(self):
        """Test singular vortex type."""
        bridge = VortexQuantumBridge(vortex_type=VortexType.SINGULAR)
        assert bridge.vortex_type == VortexType.SINGULAR
    
    def test_rankine_vortex(self):
        """Test Rankine vortex type."""
        bridge = VortexQuantumBridge(vortex_type=VortexType.RANKINE)
        assert bridge.vortex_type == VortexType.RANKINE
    
    def test_lamb_oseen_vortex(self):
        """Test Lamb-Oseen vortex type."""
        bridge = VortexQuantumBridge(vortex_type=VortexType.LAMB_OSEEN)
        assert bridge.vortex_type == VortexType.LAMB_OSEEN


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
