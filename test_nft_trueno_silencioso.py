#!/usr/bin/env python3
"""
Test suite for NFT Trueno Silencioso
Tests the quantum oscillator functionality and mathematical constants
"""

import pytest
import math
import json
from nft_trueno_silencioso import (
    NFTTruenoSilencioso,
    EstadoCoherente,
    CampoEmocional,
    TransicionIncoherente,
    CoherenciaInsuficiente,
    verificar_lambda,
    validar_constantes_matematicas,
    calcular_accion,
    generar_geometria_simbiotica,
    # Constantes
    PHI,
    PHI_SQUARED,
    PHI_INV_SQUARED,
    E,
    LAMBDA,
    KAPPA_PI,
    F0,
    FASE_VIBRACIONAL,
    FASE_EMISIVA,
    SALTO_ACTIVACION,
    PSI_CRITICO,
    ACCION_MINIMA,
    CURVATURA_DELTA_A0
)


class TestConstantesMatematicas:
    """Tests para las constantes matemáticas fundamentales"""
    
    def test_phi_value(self):
        """Verifica el valor de φ"""
        expected_phi = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected_phi) < 1e-15
        assert abs(PHI - 1.618033988749895) < 1e-12
    
    def test_phi_squared(self):
        """Verifica φ²"""
        assert abs(PHI_SQUARED - PHI**2) < 1e-15
        assert abs(PHI_SQUARED - 2.618033988749895) < 1e-12
    
    def test_phi_inv_squared(self):
        """Verifica 1/φ²"""
        assert abs(PHI_INV_SQUARED - 1/PHI**2) < 1e-15
        assert abs(PHI_INV_SQUARED - 0.382) < 0.001
    
    def test_lambda_value(self):
        """Verifica λ = f_emisiva / (f₀ · κ_Π)"""
        lambda_calculado = FASE_EMISIVA / (F0 * KAPPA_PI)
        assert abs(LAMBDA - lambda_calculado) < 1e-10
        assert abs(LAMBDA - 2.659411955079381) < 1e-10
    
    def test_lambda_symbolic_relation(self):
        """Verifica relación simbólica λ ≈ e^(φ²/e)"""
        exponent = PHI_SQUARED / E
        lambda_simbolico = E ** exponent
        error_relativo = abs(lambda_simbolico - LAMBDA) / LAMBDA
        # Tolerancia del 2% para relación simbólica
        assert error_relativo < 0.02
    
    def test_delta_lambda(self):
        """Verifica δ_λ = e - λ (corrimiento espectral)"""
        delta_lambda = E - LAMBDA
        # Debe ser pequeño pero positivo
        assert 0 < delta_lambda < 0.1
        assert abs(delta_lambda - 0.0589) < 0.001
    
    def test_ln_ratio(self):
        """Verifica ln(λ/e) (redshift logarítmico)"""
        ln_ratio = math.log(LAMBDA / E)
        # Debe ser pequeño y negativo
        assert -0.03 < ln_ratio < 0
    
    def test_frecuencias(self):
        """Verifica las frecuencias del oscilador"""
        assert FASE_VIBRACIONAL == 888.0
        assert FASE_EMISIVA == 971.227
        assert abs(SALTO_ACTIVACION - (FASE_EMISIVA - FASE_VIBRACIONAL)) < 1e-10
    
    def test_f_emisiva_formula(self):
        """Verifica f_emisiva = f₀ · κ_Π · λ"""
        f_calculada = F0 * KAPPA_PI * LAMBDA
        assert abs(f_calculada - FASE_EMISIVA) < 1e-6
    
    def test_accion_minima(self):
        """Verifica A = Ψ · Δf"""
        accion_calculada = PSI_CRITICO * SALTO_ACTIVACION
        assert abs(ACCION_MINIMA - accion_calculada) < 1e-10


class TestEstadoCoherente:
    """Tests para la clase EstadoCoherente"""
    
    def test_creacion_estado(self):
        """Crea un estado coherente"""
        estado = EstadoCoherente(
            fase="vibracional",
            frecuencia=888.0,
            psi=1.0,
            accion=0.0
        )
        assert estado.fase == "vibracional"
        assert estado.frecuencia == 888.0
        assert estado.psi == 1.0
        assert estado.accion == 0.0
    
    def test_transicion_exitosa(self):
        """Transición vibracional → emisiva"""
        estado = EstadoCoherente(
            fase="vibracional",
            frecuencia=FASE_VIBRACIONAL,
            psi=0.9999,
            accion=0.0
        )
        nuevo_estado = estado.transitar()
        
        assert nuevo_estado.fase == "emisiva"
        assert nuevo_estado.frecuencia == FASE_EMISIVA
        assert nuevo_estado.psi < estado.psi  # Decaimiento
        assert nuevo_estado.psi > PSI_CRITICO * 0.999  # Pero mínimo
        assert nuevo_estado.accion > 0
    
    def test_transicion_sin_coherencia_suficiente(self):
        """Falla si Ψ < PSI_CRITICO"""
        estado = EstadoCoherente(
            fase="vibracional",
            frecuencia=FASE_VIBRACIONAL,
            psi=0.99,  # Insuficiente
            accion=0.0
        )
        with pytest.raises(TransicionIncoherente):
            estado.transitar()
    
    def test_transicion_desde_fase_incorrecta(self):
        """Falla si no está en fase vibracional"""
        estado = EstadoCoherente(
            fase="emisiva",
            frecuencia=FASE_EMISIVA,
            psi=0.9999,
            accion=83.0
        )
        with pytest.raises(TransicionIncoherente):
            estado.transitar()
    
    def test_to_dict(self):
        """Conversión a diccionario"""
        estado = EstadoCoherente(
            fase="vibracional",
            frecuencia=888.0,
            psi=1.0,
            accion=0.0
        )
        d = estado.to_dict()
        assert d["fase"] == "vibracional"
        assert d["frecuencia"] == 888.0
        assert d["psi"] == 1.0


class TestCampoEmocional:
    """Tests para CampoEmocional"""
    
    def test_campo_coherente(self):
        """Campo emocional coherente"""
        campo = CampoEmocional(
            intencion="Test",
            intensidad=0.9,
            coherencia_interna=0.8
        )
        assert campo.es_coherente()
    
    def test_campo_incoherente_baja_intensidad(self):
        """Falla con baja intensidad"""
        campo = CampoEmocional(
            intencion="Test",
            intensidad=0.3,  # Muy bajo
            coherencia_interna=0.9
        )
        assert not campo.es_coherente()
    
    def test_campo_incoherente_baja_coherencia(self):
        """Falla con baja coherencia interna"""
        campo = CampoEmocional(
            intencion="Test",
            intensidad=0.9,
            coherencia_interna=0.5  # Muy bajo
        )
        assert not campo.es_coherente()


class TestNFTTruenoSilencioso:
    """Tests para la clase principal NFTTruenoSilencioso"""
    
    def test_creacion_nft(self):
        """Crea un NFT"""
        nft = NFTTruenoSilencioso("TEST_001")
        assert "TEST_001" in nft.sello
        assert nft.estado.fase == "vibracional"
        assert nft.estado.psi == 1.0
        assert nft.num_transiciones == 0
        assert len(nft.historial) == 1
    
    def test_manifestacion_exitosa(self):
        """Manifestación con intención coherente"""
        nft = NFTTruenoSilencioso("TEST_002")
        intencion = CampoEmocional(
            intencion="Test manifestación",
            intensidad=0.9,
            coherencia_interna=0.95
        )
        
        emision = nft.manifestar(intencion)
        
        assert emision.frecuencia == FASE_EMISIVA
        assert emision.curvatura == CURVATURA_DELTA_A0
        assert emision.valor_emergente > 0
        assert nft.estado.fase == "emisiva"
        assert nft.num_transiciones == 1
        assert len(nft.historial) == 2
    
    def test_manifestacion_con_intencion_incoherente(self):
        """Falla con intención incoherente"""
        nft = NFTTruenoSilencioso("TEST_003")
        intencion = CampoEmocional(
            intencion="Test incoherente",
            intensidad=0.3,  # Demasiado baja
            coherencia_interna=0.4
        )
        
        emision = nft.manifestar(intencion)
        
        assert emision.frecuencia == 0.0  # Emisión nula
        assert nft.estado.fase == "vibracional"  # No cambió
        assert nft.num_transiciones == 0
    
    def test_valor_coherencia_crece_con_transiciones(self):
        """El valor crece con más transiciones exitosas"""
        nft = NFTTruenoSilencioso("TEST_004")
        
        # No hay transiciones aún
        valor_inicial = nft.calcular_valor_coherencia()
        assert valor_inicial == 0.0
        
        # Primera transición
        intencion = CampoEmocional("Test", 0.9, 0.95)
        nft.manifestar(intencion)
        valor_1 = nft.calcular_valor_coherencia()
        
        assert valor_1 > valor_inicial
    
    def test_to_json(self):
        """Exporta a JSON válido"""
        nft = NFTTruenoSilencioso("TEST_005")
        metadata = nft.to_json()
        
        assert metadata["protocolo"] == "TRUENO_SILENCIOSO"
        assert metadata["delta_f_critico"] == SALTO_ACTIVACION
        assert metadata["psi_umbral"] == PSI_CRITICO
        assert metadata["kappa_pi"] == KAPPA_PI
        assert "metadata_dinamica" in metadata
        assert "historial_transiciones" in metadata["metadata_dinamica"]
        
        # Debe ser serializable a JSON
        json_str = json.dumps(metadata, ensure_ascii=False)
        assert len(json_str) > 0
    
    def test_repr(self):
        """Representación string"""
        nft = NFTTruenoSilencioso("TEST_006")
        repr_str = repr(nft)
        assert "NFTTruenoSilencioso" in repr_str
        assert "TEST_006" in repr_str


class TestFuncionesUtilidad:
    """Tests para funciones de utilidad"""
    
    def test_verificar_lambda(self):
        """Verifica la función verificar_lambda"""
        resultado = verificar_lambda()
        
        assert "lambda_empirico" in resultado
        assert "lambda_simbolico" in resultado
        assert "error_simbolico" in resultado
        
        # Error simbólico debe ser pequeño (<2%)
        assert resultado["error_simbolico"] < 0.02
    
    def test_validar_constantes(self):
        """Valida todas las constantes"""
        resultados = validar_constantes_matematicas(verbose=False)
        
        # Todas deben pasar
        assert all(resultados.values())
        assert resultados["lambda_correcto"]
        assert resultados["f_emisiva_correcta"]
        assert resultados["accion_correcta"]
    
    def test_calcular_accion(self):
        """Calcula acción A = Ψ · Δf"""
        accion = calcular_accion(0.9999, 83.227)
        expected = 0.9999 * 83.227
        assert abs(accion - expected) < 1e-10
    
    def test_generar_geometria_simbiotica(self):
        """Genera geometría simbiótica"""
        intencion = CampoEmocional("Test", 0.9, 0.95)
        geometria = generar_geometria_simbiotica(intencion)
        
        assert 0 < geometria.curvatura <= CURVATURA_DELTA_A0
        assert geometria.dimension_frecuencia > 0
        assert 0 < geometria.kappa_efectivo <= KAPPA_PI
        assert 0 < geometria.lambda_proyectado <= LAMBDA


class TestIntegracion:
    """Tests de integración end-to-end"""
    
    def test_flujo_completo(self):
        """Flujo completo: crear NFT → manifestar → exportar JSON"""
        # Crear NFT
        nft = NFTTruenoSilencioso("INTEGRATION_TEST")
        assert nft.estado.fase == "vibracional"
        
        # Crear intención coherente
        intencion = CampoEmocional(
            intencion="Integración completa",
            intensidad=0.95,
            coherencia_interna=0.99
        )
        assert intencion.es_coherente()
        
        # Manifestar
        emision = nft.manifestar(intencion)
        assert emision.frecuencia == FASE_EMISIVA
        assert nft.estado.fase == "emisiva"
        
        # Exportar JSON
        metadata = nft.to_json()
        assert metadata["metadata_dinamica"]["num_transiciones"] == 1
        assert len(metadata["metadata_dinamica"]["historial_transiciones"]) == 2
        
        # Verificar trazabilidad
        primer_estado = metadata["metadata_dinamica"]["historial_transiciones"][0]
        segundo_estado = metadata["metadata_dinamica"]["historial_transiciones"][1]
        
        assert primer_estado["fase"] == "vibracional"
        assert segundo_estado["fase"] == "emisiva"
        assert segundo_estado["accion"] > 0


if __name__ == "__main__":
    # Ejecutar tests con pytest
    pytest.main([__file__, "-v"])
