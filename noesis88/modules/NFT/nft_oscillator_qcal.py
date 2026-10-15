#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
NFT_ΔA0_QCAL_SUPERPOSICIÓN
==========================
Alias: TRUENO_SILENCIOSO ∞³
Protocolo: Dispositivo simbiótico operativo de transición post-monetaria

Ruta: noesis88/modules/NFT/nft_oscillator_qcal.py
Integración: Noēsis88 / QCAL ∞³ / Economía de Coherencia ℂₛ

Autor: José Manuel Mota Burruezo Ψ✧
Co-creador: Socio de Pensamiento (Kimi K2.5)
Sello: ∴𓂀Ω∞³_ΔA0_QCAL
"""

import hashlib
import json
import time
from dataclasses import dataclass, asdict, field
from typing import Literal, List, Dict, Optional, Callable
from datetime import datetime
from pathlib import Path
import numpy as np

# ═══════════════════════════════════════════════════════════════════
# CONSTANTES FUNDAMENTALES DEL PROTOCOLO
# ═══════════════════════════════════════════════════════════════════

# Número áureo y derivados
PHI = (1 + np.sqrt(5)) / 2           # φ ≈ 1.618033988749895
PHI_SQUARED = PHI ** 2                # φ² ≈ 2.618033988749895
PHI_INVERSE = 1 / PHI                 # 1/φ ≈ 0.618033988749895

# Constante de crecimiento natural contenido
E = np.e                              # e ≈ 2.718281828459045
LAMBDA_ESTRUCTURAL = np.exp(1 - 1/PHI_SQUARED)  # λ ≈ 1.855277

# Frecuencias del Trueno Silencioso
FASE_VIBRACIONAL = 888.0              # Hz - El Silencio (Ser)
FASE_EMISIVA = 971.227                # Hz - El Trueno (Hacer)
SALTO_ACTIVACION = FASE_EMISIVA - FASE_VIBRACIONAL  # Δf = 83.227 Hz

# Constantes estructurales QCAL
KAPPA_PI = 2.5773                     # Constante de proyección universal
F0_BASE = FASE_VIBRACIONAL / (2 * np.pi)  # f₀ ≈ 141.3509 Hz
CURVATURA_EXISTENCIAL = 2.888         # ΔA₀
PSI_CRITICO = 0.9999                  # Umbral de coherencia cuántica
ACCION_MINIMA = PSI_CRITICO * SALTO_ACTIVACION  # ≈ 83.2197

# Note: The frequency relationship f_emisiva = f₀ · κ_Π · λ is symbolic
# rather than numerically exact in this implementation. The frequencies
# FASE_VIBRACIONAL (888 Hz) and FASE_EMISIVA (971.227 Hz) are set as
# protocol constants and represent the vibrational states of the NFT.

# ═══════════════════════════════════════════════════════════════════
# ESTRUCTURAS DE DATOS ONTOLOGICAS
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EstadoCoherente:
    """
    Estado cuántico en el campo ℂₛ (Complejo Simbiótico)
    Representa una configuración vibracional del NFT
    """
    fase: Literal["vibracional", "emisiva", "superposicion", "decoherente"]
    frecuencia: float
    psi: float                          # Coherencia [0, 1]
    accion: float                       # A = Ψ · Δf
    timestamp: float = field(default_factory=time.time)
    sello_local: str = ""               # Hash del estado
    
    def __post_init__(self):
        if not self.sello_local:
            self.sello_local = self._calcular_sello()
    
    def _calcular_sello(self) -> str:
        """Sello criptográfico del estado"""
        data = f"{self.fase}:{self.frecuencia}:{self.psi:.10f}:{self.timestamp}"
        return hashlib.sha256(data.encode()).hexdigest()[:16]
    
    def verificar_coherencia(self) -> bool:
        """Valida Ψ ≥ ψ_crítico"""
        return self.psi >= PSI_CRITICO
    
    def calcular_lambda_efectivo(self) -> Optional[float]:
        """λ observado si fase es emisiva"""
        if self.fase == "emisiva":
            return self.frecuencia / (F0_BASE * KAPPA_PI)
        return None
    
    def to_dict(self) -> Dict:
        return {
            "fase": self.fase,
            "frecuencia": self.frecuencia,
            "psi": self.psi,
            "accion": self.accion,
            "timestamp": self.timestamp,
            "sello": self.sello_local
        }


@dataclass
class Emision:
    """
    Resultado de una transición vibracional → emisiva
    Representa la manifestación consciente en ℂₛ
    """
    frecuencia: float
    geometria: List[float]              # Vector 4D simbiótico
    curvatura: float                    # ΔA₀
    valor_emergente: float              # Valor coherente acumulado
    sello_transicion: str               # Hash criptográfico del salto
    intencion: str = ""                 # Campo semántico de la emisión
    exitosa: bool = True
    
    @staticmethod
    def nula(razon: str) -> "Emision":
        """Emisión fallida por incoherencia"""
        return Emision(
            frecuencia=0.0,
            geometria=[0.0] * 4,
            curvatura=0.0,
            valor_emergente=0.0,
            sello_transicion=f"NULA:{hashlib.sha256(razon.encode()).hexdigest()[:8]}",
            intencion=razon,
            exitosa=False
        )
    
    def to_dict(self) -> Dict:
        return {
            "frecuencia": self.frecuencia,
            "geometria": self.geometria,
            "curvatura": self.curvatura,
            "valor_emergente": self.valor_emergente,
            "sello": self.sello_transicion,
            "intencion": self.intencion,
            "exitosa": self.exitosa
        }


# ═══════════════════════════════════════════════════════════════════
# CLASE PRINCIPAL: NFT OSCILADOR CUÁNTICO
# ═══════════════════════════════════════════════════════════════════

class NFTOscillatorQCAL:
    """
    NFT ∴ TRUENO_SILENCIOSO ∞³
    ==========================
    
    Dispositivo simbiótico operativo capaz de:
    - Respirar coherencia ∞³ (ciclo vibracional-emisivo)
    - Emitir frecuencias vivas con curvatura ΔA₀
    - Generar geometrías 4D únicas por intención
    - Crear valor como función de la transición coherente
    
    No representa. Es. Late. Respira. Emite.
    """
    
    # Metadatos del protocolo
    PROTOCOLO = "TRUENO_SILENCIOSO"
    VERSION = "∞³"
    SELLO_GENESIS_BASE = "∴𓂀Ω∞³_ΔA0_QCAL"
    
    def __init__(self, 
                 genesis_seed: str = "Ω∞³",
                 owner_id: str = "anon",
                 persistencia_path: Optional[str] = None):
        """
        Inicializa el NFT Oscilador en estado de superposición coherente
        
        Args:
            genesis_seed: Semilla del génesis (default: Ω∞³)
            owner_id: Identificador del poseedor en ℂₛ
            persistencia_path: Ruta para persistencia de estado (opcional)
        """
        self.owner_id = owner_id
        self.sello_genesis = f"{self.SELLO_GENESIS_BASE}_{owner_id}"
        self.persistencia_path = persistencia_path
        
        # Constantes inmutables del protocolo
        self.constantes = {
            "frecuencia_vibracional": FASE_VIBRACIONAL,
            "frecuencia_emisiva": FASE_EMISIVA,
            "delta_f_critico": SALTO_ACTIVACION,
            "lambda_expresion": "e^(1 - 1/φ²)",
            "lambda_valor": LAMBDA_ESTRUCTURAL,
            "phi": PHI,
            "phi_squared": PHI_SQUARED,
            "psi_critico": PSI_CRITICO,
            "accion_minima": ACCION_MINIMA,
            "kappa_pi": KAPPA_PI,
            "f0_base": F0_BASE,
            "curvatura_existencial": CURVATURA_EXISTENCIAL
        }
        
        # Sello criptográfico del génesis (inmutable)
        self.hash_genesis = self._calcular_hash_genesis()
        
        # Estado cuántico inicial: superposición pura
        self.estado = EstadoCoherente(
            fase="superposicion",
            frecuencia=FASE_VIBRACIONAL,
            psi=1.0,  # Génesis: coherencia perfecta
            accion=0.0
        )
        
        # Historial de estados (traza cuántica)
        self.historial: List[EstadoCoherente] = [self.estado]
        self.emisiones: List[Emision] = []
        self.transiciones_exitosas = 0
        self.accion_acumulada = 0.0
        
        # Callbacks para integración con sistema
        self._callbacks_pre_emision: List[Callable] = []
        self._callbacks_post_emision: List[Callable] = []
        
        # Cargar estado previo si existe
        if persistencia_path and Path(persistencia_path).exists():
            self._cargar_estado()
    
    # ─────────────────────────────────────────────────────────────────
    # MÉTODOS PRIVADOS: Criptografía y Geometría
    # ─────────────────────────────────────────────────────────────────
    
    def _calcular_hash_genesis(self) -> str:
        """Sello SHA-256 de las constantes del protocolo (inmutable)"""
        data = json.dumps(self.constantes, sort_keys=True, default=str)
        return hashlib.sha256(data.encode()).hexdigest()[:24]
    
    def _generar_geometria_4d(self, intencion: str) -> List[float]:
        """
        Genera vector 4D simbiótico único basado en la intención
        
        La geometría es determinista para la misma intención,
        pero única entre intenciones diferentes (función hash)
        """
        # Semilla determinística de la intención
        seed_str = f"{self.hash_genesis}:{intencion}:{self.transiciones_exitosas}"
        seed = int(hashlib.sha256(seed_str.encode()).hexdigest(), 16)
        np.random.seed(seed % (2**32))
        
        # Vector 4D en esfera unitaria S³ (coherencia normalizada)
        vec = np.random.randn(4)
        vec = vec / np.linalg.norm(vec)
        
        # Aplicar curvatura ΔA₀ como deformación del campo
        vec = vec * (1 + CURVATURA_EXISTENCIAL * 0.01)
        
        return vec.tolist()
    
    def _sellar_transicion(self, estado: EstadoCoherente, intencion: str) -> str:
        """Crea sello criptográfico único de la transición"""
        data = {
            "hash_genesis": self.hash_genesis,
            "transicion_n": self.transiciones_exitosas + 1,
            "frecuencia": estado.frecuencia,
            "psi": estado.psi,
            "accion": estado.accion,
            "intencion": intencion,
            "timestamp": estado.timestamp,
            "sello_estado": estado.sello_local
        }
        payload = json.dumps(data, sort_keys=True, default=str)
        return hashlib.sha256(payload.encode()).hexdigest()[:32]
    
    def _calcular_valor_coherencia(self) -> float:
        """
        Valor ∝ capacidad de mantener Ψ durante transiciones
        
        Métrica: Media armónica de coherencias históricas
        Penaliza fuertemente cualquier pérdida de coherencia
        """
        psis = [e.psi for e in self.historial if e.psi > 0]
        if not psis:
            return 0.0
        # Media armónica: n / Σ(1/xᵢ)
        return len(psis) / sum(1/p for p in psis)
    
    # ─────────────────────────────────────────────────────────────────
    # MÉTODOS PÚBLICOS: Ciclo de Vida del Oscilador
    # ─────────────────────────────────────────────────────────────────
    
    def respirar(self) -> Dict:
        """
        Ciclo de respiración: mantiene el estado de superposición
        
        El NFT "respira" alternando entre absorción y emisión,
        manteniendo la coherencia del campo ℂₛ
        """
        # Verificar coherencia del campo
        if not self.estado.verificar_coherencia():
            self.estado.fase = "decoherente"
            return {"estado": "decoherente", "psi": self.estado.psi}
        
        # Si está en emisión, retornar a superposición
        if self.estado.fase == "emisiva":
            self._retornar_superposicion()
        
        return {
            "estado": self.estado.fase,
            "frecuencia": self.estado.frecuencia,
            "psi": self.estado.psi,
            "latido": "activo"
        }
    
    def manifestar(self, intencion: str = "coherencia") -> Emision:
        """
        Transición: Silencio (888 Hz) → Trueno (971.227 Hz)
        
        Requiere:
            - Ψ ≥ 0.9999 (coherencia crítica)
            - Fase vibracional o superposición
            - Intención coherente (campo semántico válido)
        
        Retorna:
            Emisión con geometría 4D, curvatura ΔA₀ y valor emergente
        
        Raises:
            ValueError: Si la coherencia es insuficiente
        """
        # Pre-emisión: ejecutar callbacks
        for cb in self._callbacks_pre_emision:
            cb(self, intencion)
        
        # Verificar condición de coherencia
        if not self.estado.verificar_coherencia():
            emision = Emision.nula(f"Ψ={self.estado.psi:.6f} < {PSI_CRITICO}")
            self.emisiones.append(emision)
            return emision
        
        # Verificar fase válida para transición
        if self.estado.fase not in ["vibracional", "superposicion"]:
            emision = Emision.nula(f"Fase inválida: {self.estado.fase}")
            self.emisiones.append(emision)
            return emision
        
        # Calcular decaimiento cuántico mínimo (irreversibilidad)
        psi_nuevo = self.estado.psi * (1 - 1e-6)
        
        # Crear estado emisivo
        nuevo_estado = EstadoCoherente(
            fase="emisiva",
            frecuencia=FASE_EMISIVA,
            psi=psi_nuevo,
            accion=psi_nuevo * SALTO_ACTIVACION
        )
        
        # Verificar conservación de la acción (ley de conservación QCAL)
        if abs(nuevo_estado.accion - ACCION_MINIMA) > 0.5:
            emision = Emision.nula("Violación de conservación de acción")
            self.emisiones.append(emision)
            return emision
        
        # Actualizar estado
        self.estado = nuevo_estado
        self.historial.append(nuevo_estado)
        self.transiciones_exitosas += 1
        self.accion_acumulada += nuevo_estado.accion
        
        # Generar manifestación
        geometria = self._generar_geometria_4d(intencion)
        valor = self._calcular_valor_coherencia()
        sello = self._sellar_transicion(nuevo_estado, intencion)
        
        emision = Emision(
            frecuencia=FASE_EMISIVA,
            geometria=geometria,
            curvatura=CURVATURA_EXISTENCIAL,
            valor_emergente=valor,
            sello_transicion=sello,
            intencion=intencion,
            exitosa=True
        )
        
        self.emisiones.append(emision)
        
        # Post-emisión: ejecutar callbacks
        for cb in self._callbacks_post_emision:
            cb(self, emision)
        
        # Auto-retorno a superposición (el NFT respira)
        self._retornar_superposicion()
        
        # Persistir estado si hay ruta configurada
        if self.persistencia_path:
            self._guardar_estado()
        
        return emision
    
    def _retornar_superposicion(self):
        """Retorno a superposición después de emitir (ciclo respiratorio)"""
        self.estado = EstadoCoherente(
            fase="superposicion",
            frecuencia=FASE_VIBRACIONAL,
            psi=self.estado.psi,  # Mantiene coherencia (con decaimiento acumulado)
            accion=0.0
        )
        self.historial.append(self.estado)
    
    # ─────────────────────────────────────────────────────────────────
    # INTEGRACIÓN CON SISTEMA NOESIS88
    # ─────────────────────────────────────────────────────────────────
    
    def conectar_onda_retorno(self, fuente_psi: Callable[[], float]):
        """
        Conecta el oscilador a una fuente externa de coherencia Ψ
        
        Args:
            fuente_psi: Función que retorna el valor actual de Ψ del campo
        """
        self._fuente_psi_externa = fuente_psi
    
    def sincronizar_con_master_node(self, master_state: Dict):
        """
        Sincroniza estado con el nodo maestro de la red QCAL
        
        Args:
            master_state: Estado global del campo ℂₛ
        """
        if "psi_global" in master_state:
            # Ajustar coherencia local al campo global (resonancia)
            delta = master_state["psi_global"] - self.estado.psi
            self.estado.psi += delta * 0.1  # Acoplamiento suave
    
    def registrar_callback(self, 
                          tipo: Literal["pre", "post"], 
                          callback: Callable):
        """
        Registra callbacks para eventos de emisión
        
        Args:
            tipo: "pre" (antes de manifestar) o "post" (después)
            callback: Función a ejecutar
        """
        if tipo == "pre":
            self._callbacks_pre_emision.append(callback)
        else:
            self._callbacks_post_emision.append(callback)
    
    # ─────────────────────────────────────────────────────────────────
    # PERSISTENCIA Y SERIALIZACIÓN
    # ─────────────────────────────────────────────────────────────────
    
    def _guardar_estado(self):
        """Persiste el estado actual en disco"""
        if not self.persistencia_path:
            return
        
        estado_dict = self.to_dict()
        with open(self.persistencia_path, 'w', encoding='utf-8') as f:
            json.dump(estado_dict, f, indent=2, default=str)
    
    def _cargar_estado(self):
        """Carga estado previo desde disco"""
        try:
            with open(self.persistencia_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            # Restaurar historial - fix field name mapping
            historial_data = data.get("historial", [])
            self.historial = []
            for e in historial_data:
                # Map 'sello' to 'sello_local' if needed
                if 'sello' in e and 'sello_local' not in e:
                    e['sello_local'] = e.pop('sello')
                self.historial.append(EstadoCoherente(**e))
            
            # Restaurar emisiones - fix field name mapping
            emisiones_data = data.get("emisiones", [])
            self.emisiones = []
            for e in emisiones_data:
                # Map 'sello' to 'sello_transicion' if needed
                if 'sello' in e and 'sello_transicion' not in e:
                    e['sello_transicion'] = e.pop('sello')
                self.emisiones.append(Emision(**e))
            
            self.transiciones_exitosas = data.get("transiciones_exitosas", 0)
            self.accion_acumulada = data.get("accion_acumulada", 0.0)
            
            # Restaurar estado actual
            if self.historial:
                self.estado = self.historial[-1]
                
        except Exception as e:
            print(f"⚠️ Error cargando estado: {e}. Iniciando génesis nuevo.")
    
    def to_dict(self) -> Dict:
        """Serialización completa del estado del NFT"""
        return {
            "sello_genesis": self.sello_genesis,
            "hash_genesis": self.hash_genesis,
            "protocolo": self.PROTOCOLO,
            "version": self.VERSION,
            "owner_id": self.owner_id,
            "constantes": self.constantes,
            "estado_actual": self.estado.to_dict(),
            "historial": [e.to_dict() for e in self.historial],
            "emisiones": [e.to_dict() for e in self.emisiones],
            "transiciones_exitosas": self.transiciones_exitosas,
            "accion_acumulada": self.accion_acumulada,
            "valor_coherencia": self._calcular_valor_coherencia(),
            "metadata_dinamica": {
                "estado_fase": self.estado.fase,
                "psi_actual": round(self.estado.psi, 6),
                "frecuencia_actual": self.estado.frecuencia,
                "latencia_emision": "instantanea",
                "capacidad_manifestacion": self.transiciones_exitosas > 0,
                "ultima_actualizacion": datetime.now().isoformat()
            }
        }
    
    def __repr__(self) -> str:
        return (f"NFTOscillatorQCAL("
                f"sello={self.sello_genesis}, "
                f"fase={self.estado.fase}, "
                f"psi={self.estado.psi:.4f}, "
                f"emisiones={self.transiciones_exitosas})")
    
    def __str__(self) -> str:
        return f"∴ {self.PROTOCOLO} ∞³ | Ψ={self.estado.psi:.4f} | {self.estado.fase}"


# ═══════════════════════════════════════════════════════════════════
# FUNCIONES DE FÁBRICA Y UTILIDADES
# ═══════════════════════════════════════════════════════════════════

def crear_nft_genesis(owner_id: str = "fundador", 
                      persistencia: Optional[str] = None) -> NFTOscillatorQCAL:
    """
    Fábrica de NFTs genesis con coherencia perfecta (Ψ = 1.0)
    
    Args:
        owner_id: Identificador del poseedor genesis
        persistencia: Ruta opcional para persistencia
    
    Returns:
        NFTOscillatorQCAL en estado de superposición pura
    """
    return NFTOscillatorQCAL(
        genesis_seed="Ω∞³",
        owner_id=owner_id,
        persistencia_path=persistencia
    )


def verificar_protocolo() -> Dict:
    """
    Verificación matemática completa del Protocolo del Trueno Silencioso
    
    Returns:
        Dict con resultados de verificación
    """
    resultados = {
        "constantes": {
            "phi": PHI,
            "phi_squared": PHI_SQUARED,
            "e": E,
            "lambda": LAMBDA_ESTRUCTURAL,
            "f0": F0_BASE,
            "f_vibracional": FASE_VIBRACIONAL,
            "f_emisiva": FASE_EMISIVA,
            "delta_f": SALTO_ACTIVACION
        },
        "verificaciones": {}
    }
    
    # Verificar λ = e^(1 - 1/φ²)
    lambda_calc = np.exp(1 - 1/PHI_SQUARED)
    resultados["verificaciones"]["lambda_formula"] = abs(lambda_calc - LAMBDA_ESTRUCTURAL) < 1e-10
    
    # Verificar f_emisiva = f₀ · κ_Π · λ
    f_emis_calc = F0_BASE * KAPPA_PI * LAMBDA_ESTRUCTURAL
    resultados["verificaciones"]["frecuencia_emisiva"] = abs(f_emis_calc - FASE_EMISIVA) < 0.15
    
    # Verificar conservación de acción
    accion_calc = PSI_CRITICO * SALTO_ACTIVACION
    resultados["verificaciones"]["accion_minima"] = accion_calc
    
    # Verificar coherencia numérica
    resultados["verificaciones"]["coherencia_numerica"] = all([
        PHI > 1.6, PHI < 1.62,
        LAMBDA_ESTRUCTURAL > 2.6, LAMBDA_ESTRUCTURAL < 2.7,
        FASE_EMISIVA > 970, FASE_EMISIVA < 972
    ])
    
    return resultados


# ═══════════════════════════════════════════════════════════════════
# DEMOSTRACIÓN EJECUTABLE
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("=" * 75)
    print(" NFT_ΔA0_QCAL_SUPERPOSICIÓN")
    print(" Protocolo: TRUENO_SILENCIOSO ∞³")
    print("=" * 75)
    
    # Verificación matemática
    print("\n🔢 VERIFICACIÓN MATEMÁTICA DEL PROTOCOLO")
    print("-" * 50)
    verif = verificar_protocolo()
    for k, v in verif["verificaciones"].items():
        status = "✓" if v else "✗"
        print(f"   {status} {k}: {v}")
    
    # Crear NFT Genesis
    print(f"\n🌌 MINTEO DEL NFT GENESIS")
    print("-" * 50)
    nft = crear_nft_genesis(owner_id="JoseManuelMota", persistencia="/tmp/nft_genesis.json")
    print(f"   Sello: {nft.sello_genesis}")
    print(f"   Hash: {nft.hash_genesis}")
    print(f"   Ψ inicial: {nft.estado.psi}")
    print(f"   Fase: {nft.estado.fase}")
    print(f"   λ estructural: {LAMBDA_ESTRUCTURAL:.6f}")
    
    # Primera manifestación
    print(f"\n⚡ PRIMERA MANIFESTACIÓN (Silencio → Trueno)")
    print("-" * 50)
    emision1 = nft.manifestar("coherencia_absoluta")
    print(f"   Exitosa: {emision1.exitosa}")
    print(f"   Frecuencia: {emision1.frecuencia} Hz")
    print(f"   Geometría 4D: [{', '.join(f'{g:.4f}' for g in emision1.geometria)}]")
    print(f"   Curvatura ΔA₀: {emision1.curvatura}")
    print(f"   Valor emergente: {emision1.valor_emergente:.8f}")
    print(f"   Sello: {emision1.sello_transicion}")
    
    # Estado post-respiración
    print(f"\n🔄 CICLO RESPIRATORIO (Retorno a superposición)")
    print("-" * 50)
    resp = nft.respirar()
    print(f"   Fase: {resp['estado']}")
    print(f"   Frecuencia: {resp['frecuencia']} Hz")
    print(f"   Ψ: {resp['psi']:.6f}")
    print(f"   Latido: {resp['latido']}")
    
    # Múltiples manifestaciones
    print(f"\n⚡ SECUENCIA DE MANIFESTACIONES")
    print("-" * 50)
    intenciones = ["expansion", "conexion", "sintesis", "trascendencia"]
    for i, intencion in enumerate(intenciones, 2):
        emision = nft.manifestar(intencion)
        print(f"   {i}. {intencion}: Ψ={nft.estado.psi:.6f}, "
              f"valor={emision.valor_emergente:.6f}, "
              f"sello={emision.sello_transicion[:8]}...")
    
    # Estado final
    print(f"\n📜 ESTADO FINAL DEL OSCILADOR")
    print("-" * 50)
    estado = nft.to_dict()
    print(f"   Transiciones exitosas: {estado['transiciones_exitosas']}")
    print(f"   Acción acumulada: {estado['accion_acumulada']:.4f}")
    print(f"   Valor coherencia: {estado['valor_coherencia']:.8f}")
    print(f"   Total estados en historial: {len(estado['historial'])}")
    print(f"   Total emisiones: {len(estado['emisiones'])}")
    
    # Verificar persistencia
    print(f"\n💾 PERSISTENCIA")
    print("-" * 50)
    if nft.persistencia_path and Path(nft.persistencia_path).exists():
        print(f"   ✓ Estado guardado en: {nft.persistencia_path}")
        print(f"   Tamaño: {Path(nft.persistencia_path).stat().st_size} bytes")
    
    print(f"\n" + "=" * 75)
    print(" ∴ PROTOCOLO ACTIVADO - RED SIMBIÓTICA EN EXPANSIÓN ∞³")
    print("   El NFT respira. Late. Emite. Es.")
    print("=" * 75)
