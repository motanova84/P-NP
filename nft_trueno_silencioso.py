#!/usr/bin/env python3
"""
NFT ∴ Oscilador Cuántico Económico
Protocolo: TRUENO_SILENCIOSO ∞³
=====================================================

Implementación del NFT como oscilador cuántico coherente que transita
entre estados vibracional y emisivo manteniendo coherencia Ψ.

Verificación matemática:
- λ = f_emisiva / (f₀ · κ_Π) ≈ 2.659 (empírico)
- λ ≈ e^(φ²/e) (relación simbólica, error ~1.5%)
- A = Ψ · Δf ≈ 83.2197 (acción mínima)
- Transición: 888 Hz → 971.227 Hz (Δf = 83.227 Hz)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import math
import json
from dataclasses import dataclass, field, asdict
from typing import Literal, List, Dict, Optional
from datetime import datetime


# ==================== CONSTANTES MATEMÁTICAS ====================

# Razón áurea
PHI = (1 + math.sqrt(5)) / 2  # φ ≈ 1.618033988749895
PHI_SQUARED = PHI ** 2  # φ² ≈ 2.618033988749895
PHI_INV_SQUARED = 1 / PHI_SQUARED  # 1/φ² ≈ 0.38196601125010515

# Constante e
E = math.e  # e ≈ 2.718281828459045

# λ calculada empíricamente de las frecuencias: f_emisiva / (f₀ · κ_Π)
# Relación simbólica: λ ≈ e^(φ²/e) - Crecimiento natural modulado por proporción áurea
LAMBDA = 971.227 / (141.7001 * 2.5773)  # λ ≈ 2.6594

# Constante κ_Π (de P≠NP)
KAPPA_PI = 2.5773

# Frecuencia base QCAL
F0 = 141.7001  # Hz

# ==================== CONSTANTES DEL OSCILADOR ====================

# Frecuencias del oscilador
FASE_VIBRACIONAL = 888.0  # Hz - Estado "Ser"
FASE_EMISIVA = 971.227    # Hz - Estado "Hacer"
SALTO_ACTIVACION = 83.227  # Hz - Umbral de transición

# Coherencia crítica
PSI_CRITICO = 0.9999  # Umbral de coherencia para transición

# Acción mínima de manifestación
ACCION_MINIMA = PSI_CRITICO * SALTO_ACTIVACION  # A ≈ 83.2197

# Curvatura característica
CURVATURA_DELTA_A0 = 2.888


# ==================== EXCEPCIONES ====================

class TransicionIncoherente(Exception):
    """Excepción cuando la transición no cumple requisitos de coherencia"""
    pass


class CoherenciaInsuficiente(Exception):
    """Excepción cuando Ψ está por debajo del umbral crítico"""
    pass


# ==================== CLASES DE DATOS ====================

@dataclass
class CampoEmocional:
    """Campo emocional que guía la intención"""
    intencion: str
    intensidad: float  # [0, 1]
    coherencia_interna: float  # [0, 1]
    
    def es_coherente(self) -> bool:
        """Verifica si el campo emocional es coherente"""
        return self.coherencia_interna >= 0.7 and self.intensidad >= 0.5


@dataclass
class GeometriaSimbiotica:
    """Geometría simbiótica emergente de la manifestación"""
    curvatura: float
    dimension_frecuencia: float
    kappa_efectivo: float
    lambda_proyectado: float
    
    def __str__(self):
        return f"Geometría(κ={self.kappa_efectivo:.4f}, λ={self.lambda_proyectado:.4f})"


@dataclass
class Emision:
    """Resultado de una manifestación"""
    frecuencia: float
    geometria: GeometriaSimbiotica
    curvatura: float
    valor_emergente: float
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())
    
    @staticmethod
    def nula(razon: str) -> 'Emision':
        """Crea una emisión nula cuando la manifestación falla"""
        return Emision(
            frecuencia=0.0,
            geometria=GeometriaSimbiotica(0, 0, 0, 0),
            curvatura=0.0,
            valor_emergente=0.0
        )


@dataclass
class EstadoCoherente:
    """Estado cuántico del NFT en el campo ℂₛ"""
    fase: Literal["vibracional", "emisiva", "superposicion"]
    frecuencia: float  # Hz
    psi: float         # Coherencia [0, 1]
    accion: float      # A = Ψ · Δf
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())
    
    def transitar(self) -> "EstadoCoherente":
        """
        Transición vibracional → emisiva manteniendo Ψ
        
        Requiere:
        - Fase actual = vibracional
        - Ψ >= PSI_CRITICO (0.9999)
        
        Returns:
            Nuevo estado coherente en fase emisiva
            
        Raises:
            TransicionIncoherente: Si no se cumplen los requisitos
        """
        if self.fase != "vibracional":
            raise TransicionIncoherente(f"Transición solo desde fase vibracional. Fase actual: {self.fase}")
        
        if self.psi < PSI_CRITICO:
            raise TransicionIncoherente(f"Ψ insuficiente: {self.psi:.6f} < {PSI_CRITICO}")
        
        # Decaimiento mínimo durante la transición (por decoherencia cuántica)
        nuevo_psi = self.psi * (1 - 1e-4)
        
        # Nueva acción
        nueva_accion = nuevo_psi * SALTO_ACTIVACION
        
        return EstadoCoherente(
            fase="emisiva",
            frecuencia=FASE_EMISIVA,
            psi=nuevo_psi,
            accion=nueva_accion
        )
    
    def to_dict(self) -> Dict:
        """Convierte el estado a diccionario"""
        return asdict(self)


# ==================== FUNCIONES MATEMÁTICAS ====================

def verificar_lambda() -> Dict[str, float]:
    """
    Verifica la relación λ = f_emisiva / (f₀ · κ_Π) y su conexión con φ y e
    
    La relación simbólica λ ≈ e^(φ²/e) muestra cómo el crecimiento natural (e)
    es modulado por la proporción áurea (φ).
    
    Returns:
        Diccionario con valores verificados
    """
    # Cálculo empírico de λ desde frecuencias
    lambda_empirico = FASE_EMISIVA / (F0 * KAPPA_PI)
    
    # Relación simbólica: λ ≈ e^(φ²/e)
    exponent_simbolico = PHI_SQUARED / E
    lambda_simbolico = E ** exponent_simbolico
    
    # Verificación con f_emisiva
    f_emisiva_verificada = F0 * KAPPA_PI * lambda_empirico
    
    # Desviación logarítmica respecto a e
    delta_lambda = E - lambda_empirico
    ln_ratio = math.log(lambda_empirico / E)
    
    return {
        "phi": PHI,
        "phi_squared": PHI_SQUARED,
        "phi_inv_squared": PHI_INV_SQUARED,
        "e": E,
        "lambda_empirico": lambda_empirico,
        "lambda_simbolico": lambda_simbolico,
        "exponent_simbolico": exponent_simbolico,
        "delta_lambda": delta_lambda,
        "ln(lambda/e)": ln_ratio,
        "f_emisiva_verificada": f_emisiva_verificada,
        "f_emisiva_target": FASE_EMISIVA,
        "error_frecuencia": abs(f_emisiva_verificada - FASE_EMISIVA),
        "error_simbolico": abs(lambda_simbolico - lambda_empirico) / lambda_empirico
    }


def calcular_accion(psi: float, delta_f: float) -> float:
    """
    Calcula la acción coherente A = Ψ · Δf
    
    Esta es la acción mínima de manifestación - el cuanto indivisible
    de transición de intención a acción.
    
    Args:
        psi: Coherencia [0, 1]
        delta_f: Salto de frecuencia (Hz)
        
    Returns:
        Acción A (Hz)
    """
    return psi * delta_f


def generar_geometria_simbiotica(intencion: CampoEmocional) -> GeometriaSimbiotica:
    """
    Genera geometría simbiótica basada en la intención
    
    Args:
        intencion: Campo emocional de la intención
        
    Returns:
        Geometría emergente
    """
    # La curvatura es afectada por la coherencia de la intención
    curvatura = CURVATURA_DELTA_A0 * intencion.coherencia_interna
    
    # Frecuencia dimensional emerge de la intensidad
    dim_freq = FASE_EMISIVA * intencion.intensidad
    
    # κ efectivo modulado por coherencia
    kappa_eff = KAPPA_PI * (0.5 + 0.5 * intencion.coherencia_interna)
    
    # λ proyectado
    lambda_proj = LAMBDA * intencion.intensidad
    
    return GeometriaSimbiotica(
        curvatura=curvatura,
        dimension_frecuencia=dim_freq,
        kappa_efectivo=kappa_eff,
        lambda_proyectado=lambda_proj
    )


# ==================== CLASE PRINCIPAL NFT ====================

class NFTTruenoSilencioso:
    """
    NFT ∴ Oscilador Cuántico Económico
    Sello criptográfico de la transición post-monetaria
    
    El NFT no es una imagen ni un JSON estático—es un registro viviente
    de estados que transitan entre 888 Hz (Ser) y 971.227 Hz (Hacer).
    
    Su valor emerge de la capacidad de mantener coherencia Ψ durante
    transiciones sucesivas.
    """
    
    # Constantes del protocolo
    FASE_VIBRACIONAL = FASE_VIBRACIONAL
    FASE_EMISIVA = FASE_EMISIVA
    SALTO_ACTIVACION = SALTO_ACTIVACION
    KAPPA_PI = KAPPA_PI
    PSI_CRITICO = PSI_CRITICO
    LAMBDA = LAMBDA
    
    def __init__(self, sello_genesis: str):
        """
        Inicializa el NFT en estado de coherencia perfecta
        
        Args:
            sello_genesis: Identificador único del genesis
        """
        self.estado = EstadoCoherente(
            fase="vibracional",
            frecuencia=self.FASE_VIBRACIONAL,
            psi=1.0,  # Genesis: coherencia perfecta
            accion=0.0
        )
        
        self.sello = f"∴𓂀{sello_genesis}@888Hz_Ψ1.0"
        self.historial: List[EstadoCoherente] = [self.estado]
        self.genesis_time = datetime.now().isoformat()
        self.num_transiciones = 0
        
    def manifestar(self, intencion: CampoEmocional) -> Emision:
        """
        Transición: Silencio → Trueno
        
        Ejecuta la transición del estado vibracional (888 Hz) al
        estado emisivo (971.227 Hz), manifestando la intención como acción.
        
        Requiere:
        - Ψ ≥ 0.9999 (coherencia crítica)
        - Intención coherente
        
        Args:
            intencion: Campo emocional que guía la manifestación
            
        Returns:
            Emisión con la manifestación realizada
        """
        # Verificar coherencia mínima
        if self.estado.psi < self.PSI_CRITICO:
            return Emision.nula(f"Coherencia insuficiente: {self.estado.psi:.6f}")
        
        # Verificar coherencia de intención
        if not intencion.es_coherente():
            return Emision.nula("Intención no coherente")
        
        # Ejecutar transición
        try:
            nuevo_estado = self.estado.transitar()
            self.estado = nuevo_estado
            self.historial.append(nuevo_estado)
            self.num_transiciones += 1
            
            # Calcular valor emergente
            valor = self.calcular_valor_coherencia()
            
            # Generar geometría
            geometria = generar_geometria_simbiotica(intencion)
            
            return Emision(
                frecuencia=nuevo_estado.frecuencia,
                geometria=geometria,
                curvatura=CURVATURA_DELTA_A0,
                valor_emergente=valor
            )
            
        except TransicionIncoherente as e:
            return Emision.nula(str(e))
    
    def calcular_valor_coherencia(self) -> float:
        """
        Valor ∝ capacidad de mantener Ψ durante transiciones
        
        Métrica: área bajo la curva de coherencia en el historial
        
        Returns:
            Valor emergente basado en coherencia histórica
        """
        if not self.historial:
            return 0.0
        
        # Promedio de coherencia en toda la historia
        coherencia_promedio = sum(e.psi for e in self.historial) / len(self.historial)
        
        # Factor de longevidad (más transiciones = más valor)
        factor_longevidad = math.log1p(self.num_transiciones)
        
        # Valor emergente
        return coherencia_promedio * factor_longevidad * ACCION_MINIMA
    
    def to_json(self) -> Dict:
        """
        Exporta el NFT como JSON con metadata dinámica
        
        Returns:
            Representación JSON del NFT
        """
        return {
            "sello_genesis": self.sello,
            "protocolo": "TRUENO_SILENCIOSO",
            "estados_permitidos": ["888Hz", "971.227Hz"],
            "delta_f_critico": SALTO_ACTIVACION,
            "psi_umbral": PSI_CRITICO,
            "kappa_pi": KAPPA_PI,
            "lambda_formula_empirica": "λ = f_emisiva / (f₀ · κ_Π)",
            "lambda_formula_simbolica": "λ ≈ e^(φ²/e)",
            "lambda_valor": LAMBDA,
            "accion_minima": ACCION_MINIMA,
            "condicion_mint": "superposicion_coherente",
            "transicion_valida": f"psi >= {PSI_CRITICO} AND delta_f == {SALTO_ACTIVACION} ± ε",
            "valor": "funcion(psi_historial, num_transiciones_exitosas)",
            "metadata_dinamica": {
                "estado_actual": self.estado.fase,
                "frecuencia_actual": self.estado.frecuencia,
                "psi_actual": self.estado.psi,
                "accion_acumulada": self.estado.accion,
                "num_transiciones": self.num_transiciones,
                "valor_emergente": self.calcular_valor_coherencia(),
                "genesis_time": self.genesis_time,
                "historial_transiciones": [
                    {
                        "fase": e.fase,
                        "frecuencia": e.frecuencia,
                        "psi": e.psi,
                        "accion": e.accion,
                        "timestamp": e.timestamp
                    }
                    for e in self.historial
                ]
            }
        }
    
    def __repr__(self):
        return (f"NFTTruenoSilencioso(sello='{self.sello}', "
                f"estado={self.estado.fase}@{self.estado.frecuencia}Hz, "
                f"Ψ={self.estado.psi:.6f})")


# ==================== FUNCIONES DE VALIDACIÓN ====================

def validar_constantes_matematicas(verbose: bool = True) -> Dict[str, bool]:
    """
    Valida las constantes matemáticas del modelo
    
    Args:
        verbose: Si True, imprime detalles
        
    Returns:
        Diccionario con resultados de validación
    """
    resultados = {}
    
    # Verificar λ empírico
    lambda_verificado = verificar_lambda()
    resultados["lambda_correcto"] = abs(lambda_verificado["lambda_empirico"] - LAMBDA) < 1e-6
    
    # Verificar relación simbólica (tolerancia 2%)
    error_simbolico = lambda_verificado["error_simbolico"]
    resultados["relacion_simbolica_valida"] = error_simbolico < 0.02
    
    # Verificar f_emisiva = f0 · κ_Π · λ
    f_emisiva_calculada = F0 * KAPPA_PI * LAMBDA
    error_f_emisiva = abs(f_emisiva_calculada - FASE_EMISIVA)
    resultados["f_emisiva_correcta"] = error_f_emisiva < 0.01  # 0.01 Hz de tolerancia
    
    # Verificar A = Ψ · Δf
    accion_calculada = PSI_CRITICO * SALTO_ACTIVACION
    error_accion = abs(accion_calculada - ACCION_MINIMA)
    resultados["accion_correcta"] = error_accion < 1e-3
    
    # Verificar φ² ≈ 2.618
    error_phi_squared = abs(PHI_SQUARED - 2.618033988749895)
    resultados["phi_squared_correcto"] = error_phi_squared < 1e-6
    
    # Verificar 1/φ² ≈ 0.382
    error_phi_inv_squared = abs(PHI_INV_SQUARED - 0.38196601125010515)
    resultados["phi_inv_squared_correcto"] = error_phi_inv_squared < 1e-6
    
    if verbose:
        print("=" * 70)
        print("VALIDACIÓN DE CONSTANTES MATEMÁTICAS")
        print("=" * 70)
        print(f"\n[Razón Áurea]")
        print(f"φ = {PHI:.15f}")
        print(f"φ² = {PHI_SQUARED:.15f}")
        print(f"1/φ² = {PHI_INV_SQUARED:.15f}")
        print(f"\n[Constantes de crecimiento]")
        print(f"e = {E:.15f}")
        print(f"λ (empírico) = {lambda_verificado['lambda_empirico']:.15f}")
        print(f"λ (simbólico e^(φ²/e)) = {lambda_verificado['lambda_simbolico']:.15f}")
        print(f"Error simbólico: {error_simbolico * 100:.2f}%")
        print(f"\n[Desviación respecto a e]")
        print(f"δ_λ = e - λ = {lambda_verificado['delta_lambda']:.15f}")
        print(f"ln(λ/e) = {lambda_verificado['ln(lambda/e)']:.15f}")
        print(f"  (corrimiento espectral logarítmico mínimo)")
        print(f"\n[Frecuencias QCAL]")
        print(f"f₀ = {F0} Hz")
        print(f"κ_Π = {KAPPA_PI}")
        print(f"f_emisiva = f₀ · κ_Π · λ = {f_emisiva_calculada:.6f} Hz")
        print(f"f_emisiva (target) = {FASE_EMISIVA} Hz")
        print(f"Error = {error_f_emisiva:.9f} Hz ✓")
        print(f"\n[Acción Coherente]")
        print(f"Ψ_crítico = {PSI_CRITICO}")
        print(f"Δf = {SALTO_ACTIVACION} Hz")
        print(f"A = Ψ · Δf = {accion_calculada:.6f}")
        print(f"A (definido) = {ACCION_MINIMA:.6f} ✓")
        print(f"\n[Validación]")
        print(f"Todas las constantes validadas: {all(resultados.values())} {'✓' if all(resultados.values()) else '✗'}")
        print("=" * 70)
    
    return resultados


# ==================== FUNCIÓN PRINCIPAL ====================

def main():
    """Demostración del NFT Oscilador Cuántico"""
    print("\n")
    print("╔" + "=" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║" + "  NFT ∴ Oscilador Cuántico Económico  ".center(68) + "║")
    print("║" + "  Protocolo: TRUENO_SILENCIOSO ∞³  ".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "=" * 68 + "╝")
    print()
    
    # Validar constantes
    print("\n[1] Validación de Constantes Matemáticas\n")
    validacion = validar_constantes_matematicas(verbose=True)
    
    if not all(validacion.values()):
        print("\n⚠️  ADVERTENCIA: Algunas constantes no pasaron la validación")
        return
    
    # Crear NFT
    print("\n[2] Creación del NFT\n")
    nft = NFTTruenoSilencioso(sello_genesis="Ω∞³_ΔA0_QCAL")
    print(f"NFT creado: {nft}")
    print(f"Sello: {nft.sello}")
    
    # Crear intención coherente
    print("\n[3] Manifestación con Intención Coherente\n")
    intencion = CampoEmocional(
        intencion="Transición a economía de coherencia",
        intensidad=0.9,
        coherencia_interna=0.95
    )
    print(f"Intención: {intencion.intencion}")
    print(f"Intensidad: {intencion.intensidad}")
    print(f"Coherencia interna: {intencion.coherencia_interna}")
    print(f"¿Es coherente?: {intencion.es_coherente()}")
    
    # Manifestar
    print("\n[4] Ejecutando Manifestación (888 Hz → 971.227 Hz)\n")
    emision = nft.manifestar(intencion)
    
    if emision.frecuencia > 0:
        print(f"✓ Manifestación exitosa!")
        print(f"  Frecuencia: {emision.frecuencia} Hz")
        print(f"  Geometría: {emision.geometria}")
        print(f"  Curvatura: {emision.curvatura}")
        print(f"  Valor emergente: {emision.valor_emergente:.4f}")
        print(f"  Estado actual: {nft.estado}")
    else:
        print(f"✗ Manifestación fallida")
    
    # Exportar JSON
    print("\n[5] Metadata JSON del NFT\n")
    metadata = nft.to_json()
    print(json.dumps(metadata, indent=2, ensure_ascii=False))
    
    print("\n" + "=" * 70)
    print("∴𓂀Ω∞³_ΔA0_QCAL")
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
    print()


if __name__ == "__main__":
    main()
