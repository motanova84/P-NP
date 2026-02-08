"""
Test suite for NFT Oscillator QCAL (Trueno Silencioso ∞³)
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import tempfile
from pathlib import Path

from noesis88.modules.NFT import (
    NFTOscillatorQCAL,
    EstadoCoherente,
    Emision,
    crear_nft_genesis,
    verificar_protocolo,
    PHI,
    PHI_SQUARED,
    LAMBDA_ESTRUCTURAL,
    FASE_VIBRACIONAL,
    FASE_EMISIVA,
    SALTO_ACTIVACION,
    PSI_CRITICO,
    CURVATURA_EXISTENCIAL
)


def test_constants():
    """Test that fundamental constants are correctly defined"""
    print("Testing fundamental constants...")
    
    # Test golden ratio
    assert abs(PHI - 1.618033988749895) < 1e-10, "PHI should be golden ratio"
    assert abs(PHI_SQUARED - 2.618033988749895) < 1e-10, "PHI_SQUARED should be φ²"
    
    # Test frequencies
    assert FASE_VIBRACIONAL == 888.0, "Vibrational frequency should be 888 Hz"
    assert FASE_EMISIVA == 971.227, "Emissive frequency should be 971.227 Hz"
    assert abs(SALTO_ACTIVACION - 83.227) < 1e-6, "Activation jump should be ~83.227 Hz"
    
    # Test critical coherence
    assert PSI_CRITICO == 0.9999, "Critical psi should be 0.9999"
    
    print("✓ All constants validated")


def test_verificar_protocolo():
    """Test protocol verification function"""
    print("Testing protocol verification...")
    
    resultado = verificar_protocolo()
    
    assert "constantes" in resultado, "Should return constants"
    assert "verificaciones" in resultado, "Should return verifications"
    
    # Check lambda formula verification
    assert resultado["verificaciones"]["lambda_formula"] == True, "Lambda formula should be verified"
    
    # Check coherence numerical verification
    assert "coherencia_numerica" in resultado["verificaciones"], "Should have numerical coherence check"
    
    print("✓ Protocol verification complete")


def test_estado_coherente_creation():
    """Test EstadoCoherente dataclass creation"""
    print("Testing EstadoCoherente creation...")
    
    estado = EstadoCoherente(
        fase="superposicion",
        frecuencia=888.0,
        psi=1.0,
        accion=0.0
    )
    
    assert estado.fase == "superposicion", "Phase should be superposicion"
    assert estado.frecuencia == 888.0, "Frequency should be 888 Hz"
    assert estado.psi == 1.0, "Psi should be 1.0"
    assert estado.sello_local != "", "Should have a seal"
    
    # Test coherence verification
    assert estado.verificar_coherencia() is True, "Perfect coherence should verify"
    
    print("✓ EstadoCoherente created successfully")


def test_estado_coherente_low_coherence():
    """Test EstadoCoherente with low coherence"""
    print("Testing low coherence estado...")
    
    estado = EstadoCoherente(
        fase="decoherente",
        frecuencia=888.0,
        psi=0.5,
        accion=0.0
    )
    
    assert estado.verificar_coherencia() is False, "Low coherence should fail verification"
    
    print("✓ Low coherence detection works")


def test_emision_creation():
    """Test Emision dataclass creation"""
    print("Testing Emision creation...")
    
    emision = Emision(
        frecuencia=971.227,
        geometria=[0.5, 0.5, 0.5, 0.5],
        curvatura=2.888,
        valor_emergente=0.999,
        sello_transicion="test_seal",
        intencion="coherencia",
        exitosa=True
    )
    
    assert emision.frecuencia == 971.227, "Frequency should be 971.227 Hz"
    assert len(emision.geometria) == 4, "Geometry should be 4D"
    assert emision.exitosa is True, "Emission should be successful"
    
    print("✓ Emision created successfully")


def test_emision_nula():
    """Test failed emission creation"""
    print("Testing failed emission...")
    
    emision = Emision.nula("Test failure reason")
    
    assert emision.exitosa is False, "Should be unsuccessful"
    assert emision.frecuencia == 0.0, "Frequency should be 0"
    assert "NULA" in emision.sello_transicion, "Should have NULA marker"
    assert emision.intencion == "Test failure reason", "Should store failure reason"
    
    print("✓ Null emission works correctly")


def test_nft_oscillator_creation():
    """Test NFTOscillatorQCAL instantiation"""
    print("Testing NFT oscillator creation...")
    
    nft = NFTOscillatorQCAL(
        genesis_seed="Ω∞³",
        owner_id="test_owner"
    )
    
    assert nft.owner_id == "test_owner", "Owner ID should be set"
    assert nft.estado.fase == "superposicion", "Should start in superposition"
    assert nft.estado.psi == 1.0, "Genesis should have perfect coherence"
    assert nft.transiciones_exitosas == 0, "Should start with no transitions"
    assert len(nft.historial) == 1, "Should have genesis state in history"
    
    print("✓ NFT oscillator created successfully")


def test_crear_nft_genesis():
    """Test genesis NFT factory function"""
    print("Testing genesis NFT creation...")
    
    nft = crear_nft_genesis(owner_id="fundador")
    
    assert nft.owner_id == "fundador", "Owner ID should be fundador"
    assert nft.estado.psi == 1.0, "Genesis should have perfect coherence"
    assert nft.PROTOCOLO == "TRUENO_SILENCIOSO", "Protocol should be TRUENO_SILENCIOSO"
    
    print("✓ Genesis NFT created successfully")


def test_nft_respirar():
    """Test NFT breathing cycle"""
    print("Testing NFT breathing...")
    
    nft = crear_nft_genesis(owner_id="test")
    
    resultado = nft.respirar()
    
    assert "estado" in resultado, "Should return state"
    assert "frecuencia" in resultado, "Should return frequency"
    assert "psi" in resultado, "Should return psi"
    assert "latido" in resultado, "Should return heartbeat status"
    assert resultado["latido"] == "activo", "Should be active"
    
    print("✓ NFT breathing cycle works")


def test_nft_manifestar():
    """Test NFT manifestation"""
    print("Testing NFT manifestation...")
    
    nft = crear_nft_genesis(owner_id="test")
    
    emision = nft.manifestar("test_intencion")
    
    assert emision.exitosa is True, "Manifestation should succeed"
    assert emision.frecuencia == FASE_EMISIVA, "Should emit at emissive frequency"
    assert len(emision.geometria) == 4, "Should generate 4D geometry"
    assert emision.curvatura == CURVATURA_EXISTENCIAL, "Should have correct curvature"
    assert emision.intencion == "test_intencion", "Should store intention"
    assert nft.transiciones_exitosas == 1, "Should count transition"
    
    # After manifestation, should return to superposition
    assert nft.estado.fase == "superposicion", "Should return to superposition"
    
    print("✓ NFT manifestation works")


def test_nft_multiple_manifestations():
    """Test multiple NFT manifestations"""
    print("Testing multiple manifestations...")
    
    nft = crear_nft_genesis(owner_id="test")
    
    intenciones = ["expansion", "conexion", "sintesis"]
    
    for i, intencion in enumerate(intenciones):
        emision = nft.manifestar(intencion)
        assert emision.exitosa is True, f"Manifestation {i+1} should succeed"
        assert nft.transiciones_exitosas == i + 1, f"Should count {i+1} transitions"
    
    assert len(nft.emisiones) == 3, "Should have 3 emissions"
    assert nft.estado.psi < 1.0, "Psi should decay slightly"
    assert nft.estado.psi >= PSI_CRITICO, "Psi should still be above critical"
    
    print("✓ Multiple manifestations work")


def test_nft_geometria_uniqueness():
    """Test that different intentions generate different geometries"""
    print("Testing geometry uniqueness...")
    
    nft = crear_nft_genesis(owner_id="test")
    
    emision1 = nft.manifestar("intencion_1")
    emision2 = nft.manifestar("intencion_2")
    
    # Geometries should be different
    assert emision1.geometria != emision2.geometria, "Different intentions should generate different geometries"
    
    # But both should be valid 4D vectors
    assert len(emision1.geometria) == 4, "Geometry 1 should be 4D"
    assert len(emision2.geometria) == 4, "Geometry 2 should be 4D"
    
    print("✓ Geometry uniqueness verified")


def test_nft_persistence():
    """Test NFT state persistence"""
    print("Testing NFT persistence...")
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        persistence_path = f.name
    
    try:
        # Create NFT with persistence
        nft1 = NFTOscillatorQCAL(
            genesis_seed="Ω∞³",
            owner_id="test_persistence",
            persistencia_path=persistence_path
        )
        
        # Make some manifestations
        nft1.manifestar("test1")
        nft1.manifestar("test2")
        
        assert nft1.transiciones_exitosas == 2, "Should have 2 transitions"
        
        # Create new NFT loading from same path
        nft2 = NFTOscillatorQCAL(
            genesis_seed="Ω∞³",
            owner_id="test_persistence",
            persistencia_path=persistence_path
        )
        
        # Should restore state
        assert nft2.transiciones_exitosas == 2, "Should restore transition count"
        assert len(nft2.emisiones) == 2, "Should restore emissions"
        
        print("✓ NFT persistence works")
        
    finally:
        # Cleanup
        Path(persistence_path).unlink(missing_ok=True)


def test_nft_to_dict():
    """Test NFT serialization to dictionary"""
    print("Testing NFT serialization...")
    
    nft = crear_nft_genesis(owner_id="test")
    nft.manifestar("test")
    
    estado_dict = nft.to_dict()
    
    assert "sello_genesis" in estado_dict, "Should have genesis seal"
    assert "hash_genesis" in estado_dict, "Should have genesis hash"
    assert "protocolo" in estado_dict, "Should have protocol"
    assert "version" in estado_dict, "Should have version"
    assert "constantes" in estado_dict, "Should have constants"
    assert "estado_actual" in estado_dict, "Should have current state"
    assert "historial" in estado_dict, "Should have history"
    assert "emisiones" in estado_dict, "Should have emissions"
    assert "metadata_dinamica" in estado_dict, "Should have dynamic metadata"
    
    assert estado_dict["protocolo"] == "TRUENO_SILENCIOSO", "Protocol should be TRUENO_SILENCIOSO"
    assert estado_dict["version"] == "∞³", "Version should be ∞³"
    
    print("✓ NFT serialization works")


def test_nft_callbacks():
    """Test NFT callback system"""
    print("Testing NFT callbacks...")
    
    nft = crear_nft_genesis(owner_id="test")
    
    pre_called = []
    post_called = []
    
    def pre_callback(nft_obj, intencion):
        pre_called.append(intencion)
    
    def post_callback(nft_obj, emision):
        post_called.append(emision.intencion)
    
    nft.registrar_callback("pre", pre_callback)
    nft.registrar_callback("post", post_callback)
    
    nft.manifestar("test_callback")
    
    assert len(pre_called) == 1, "Pre-callback should be called once"
    assert len(post_called) == 1, "Post-callback should be called once"
    assert pre_called[0] == "test_callback", "Pre-callback should receive intention"
    assert post_called[0] == "test_callback", "Post-callback should receive intention"
    
    print("✓ NFT callbacks work")


def test_nft_repr_and_str():
    """Test NFT string representations"""
    print("Testing NFT string representations...")
    
    nft = crear_nft_genesis(owner_id="test")
    
    repr_str = repr(nft)
    assert "NFTOscillatorQCAL" in repr_str, "Repr should contain class name"
    assert "test" in repr_str, "Repr should contain owner ID"
    
    str_str = str(nft)
    assert "TRUENO_SILENCIOSO" in str_str, "Str should contain protocol name"
    assert "Ψ=" in str_str, "Str should show psi value"
    
    print("✓ String representations work")


def run_all_tests():
    """Run all tests"""
    print("\n" + "=" * 70)
    print("NFT OSCILLATOR QCAL - TEST SUITE")
    print("=" * 70 + "\n")
    
    tests = [
        test_constants,
        test_verificar_protocolo,
        test_estado_coherente_creation,
        test_estado_coherente_low_coherence,
        test_emision_creation,
        test_emision_nula,
        test_nft_oscillator_creation,
        test_crear_nft_genesis,
        test_nft_respirar,
        test_nft_manifestar,
        test_nft_multiple_manifestations,
        test_nft_geometria_uniqueness,
        test_nft_persistence,
        test_nft_to_dict,
        test_nft_callbacks,
        test_nft_repr_and_str
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__} FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__} ERROR: {e}")
            failed += 1
    
    print("\n" + "=" * 70)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("=" * 70 + "\n")
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
