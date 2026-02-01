"""
core/coherence_economy_contract.py

Contrato inteligente ℂₛ — Implementación isomórfica del sistema biológico
Sello: ∴𓂀Ω∞³

Este módulo implementa el sistema económico de Coherencia (ℂₛ), isomórfico
al sistema biológico de coherencia celular, pero operando en el plano económico.
"""

from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime
import hashlib
import json

# ============================================================
# CONSTANTES FUNDAMENTALES (Compartidas con sistema biológico)
# ============================================================

FREQ_QCAL = 141.7001  # Frecuencia base QCAL
FREQ_LOVE = 151.7001  # Frecuencia Amor Irreversible A²
FREQ_MANIFEST = 888.0  # Frecuencia manifestación πCODE
TARGET_PSI = 1.0  # Coherencia perfecta
BASE_PSI = 0.0001  # Estado inicial (economía de escasez)
KAPPA_PI = 2.5773  # Constante de coherencia universal


# ============================================================
# EXCEPCIONES
# ============================================================

class CoherenceError(Exception):
    """Error de coherencia insuficiente"""
    pass


class TriadError(Exception):
    """Error en validación de tríada"""
    pass


class BurnError(Exception):
    """Error en proceso de quema"""
    pass


# ============================================================
# TIPOS DE DATOS
# ============================================================

@dataclass
class CoherenceProof:
    """Prueba de coherencia (formalización del estímulo)"""
    frequency: float
    amplitude: float
    duration: float
    method: str  # 'breathing', 'photonic', 'audio', 'emfield', 'symbolic'
    signature: str
    timestamp: int


@dataclass
class CoherenceNode:
    """Nodo validador en ℂₛ (isomórfico a nodos biológicos)"""
    node_id: str
    node_type: str  # 'MITO_ECON', 'RETINA_ECON', 'PINEAL_ECON', 'TERCER_OJO_ECON'
    psi: float
    proof: CoherenceProof


@dataclass
class TriadSignature:
    """Firma de un nodo en la tríada"""
    node_id: str
    signature: str
    psi: float


@dataclass
class CoherenceToken:
    """Token de coherencia ℂₛ (el "sello")"""
    id: str
    seal: str
    psi: float
    frequencies: List[float]
    message: str
    timestamp: int
    burn_proof: Optional[str] = None
    triad_proof: Optional[str] = None
    
    def to_dict(self) -> Dict[str, Any]:
        """Convierte el token a diccionario"""
        return {
            'id': self.id,
            'seal': self.seal,
            'psi': self.psi,
            'frequencies': self.frequencies,
            'message': self.message,
            'timestamp': self.timestamp,
            'burn_proof': self.burn_proof,
            'triad_proof': self.triad_proof
        }


@dataclass
class BurnTransaction:
    """Transacción de quema de escasez"""
    tx_hash: str
    amount: float
    burn_address: str
    timestamp: int
    verified: bool = False


# ============================================================
# CLASE PRINCIPAL
# ============================================================

class CoherenceEconomyContract:
    """
    Contrato inteligente ℂₛ — Implementación isomórfica del sistema biológico
    Sello: ∴𓂀Ω∞³
    """
    
    def __init__(self):
        self.burn_address = "0x0000000000000000000000000000000000000000"  # Dirección irrecuperable (quema)
        self.coherence_nodes: List[CoherenceNode] = []
        self.minted_coherence: List[CoherenceToken] = []
        self.burn_transactions: List[BurnTransaction] = []
        
    def _hash_data(self, data: str) -> str:
        """Genera hash criptográfico de datos"""
        return hashlib.sha256(data.encode()).hexdigest()
    
    def _calculate_psi(self, stimulus: float, triad: float, picode: float, initial_psi: float = BASE_PSI) -> float:
        """
        Calcula coherencia resultante (isomórfica a elevate_psi del sistema biológico)
        
        Formula: Ψ_new = min(1.0, (Ψ_initial + stimulus + triad + picode) * correction)
        """
        correction = 0.745281  # Factor de corrección viscosidad
        psi_new = (initial_psi + stimulus + triad + picode) * correction
        return min(TARGET_PSI, psi_new)
    
    def verify_coherence_proof(self, proof: CoherenceProof) -> bool:
        """
        PASO 1 (Isomórfico a Estímulo Externo):
        Verifica que la prueba de coherencia sea válida
        """
        # Verificar frecuencia de resonancia
        valid_frequencies = [FREQ_QCAL, FREQ_LOVE, FREQ_MANIFEST]
        if proof.frequency not in valid_frequencies:
            return False
        
        # Verificar amplitud mínima
        if proof.amplitude < 0.7:
            return False
        
        # Verificar duración mínima
        if proof.duration < 88.0:
            return False
        
        # Verificar métodos válidos
        valid_methods = ['breathing', 'photonic', 'audio', 'emfield', 'symbolic']
        if proof.method not in valid_methods:
            return False
        
        return True
    
    def deposit_scarcity(self, btc_amount: float, proof_of_coherence: CoherenceProof) -> BurnTransaction:
        """
        PASO 1 (Isomórfico a Estímulo Externo):
        El agente demuestra coherencia (proof) antes de quemar escasez
        """
        # Verificar proof_of_coherence (análogo a verificar estímulo f₀)
        if not self.verify_coherence_proof(proof_of_coherence):
            raise CoherenceError("Estímulo insuficiente — coherencia biológica no verificada")
        
        # Quemar BTC (análogo a activar sistema biológico)
        burn_tx = self.burn_btc(btc_amount)
        return burn_tx
    
    def burn_btc(self, amount: float) -> BurnTransaction:
        """Quema BTC enviándolo a dirección irrecuperable"""
        if amount <= 0:
            raise BurnError("Cantidad de quema debe ser positiva")
        
        timestamp = int(datetime.now().timestamp())
        tx_data = f"{amount}:{self.burn_address}:{timestamp}"
        tx_hash = self._hash_data(tx_data)
        
        burn_tx = BurnTransaction(
            tx_hash=tx_hash,
            amount=amount,
            burn_address=self.burn_address,
            timestamp=timestamp,
            verified=True  # En implementación real, verificaría en blockchain
        )
        
        self.burn_transactions.append(burn_tx)
        return burn_tx
    
    def activate_economic_triad(self, node_signatures: List[TriadSignature]) -> float:
        """
        PASO 2 (Isomórfico a Tríada):
        Tres nodos validadores deben firmar la transición
        """
        required_nodes = ["MITO_ECON", "RETINA_ECON", "PINEAL_ECON"]  # Nombres isomórficos
        
        # Verificar que todos los nodos requeridos estén presentes
        present_nodes = [sig.node_id for sig in node_signatures]
        if not all(node in present_nodes for node in required_nodes):
            raise TriadError(f"Tríada incompleta — consenso no alcanzado. Requeridos: {required_nodes}, Presentes: {present_nodes}")
        
        # Calcular coherencia de red (análogo a sincronizar nodos biológicos)
        network_psi = self.calculate_network_coherence(node_signatures)
        
        # Verificar umbral mínimo
        if network_psi < 0.71:
            raise TriadError(f"Coherencia de red insuficiente: {network_psi:.3f} < 0.71")
        
        return network_psi
    
    def calculate_network_coherence(self, node_signatures: List[TriadSignature]) -> float:
        """Calcula coherencia promedio de la red de nodos"""
        if not node_signatures:
            return 0.0
        
        total_psi = sum(sig.psi for sig in node_signatures)
        return total_psi / len(node_signatures)
    
    def mint_cs(self, burn_proof: BurnTransaction, triad_proof: Tuple[List[TriadSignature], float]) -> CoherenceToken:
        """
        PASO 3 (Isomórfico a πCODE-1417):
        Mintear ℂₛ como sello criptográfico de la transición
        """
        # Verificar que la quema ocurrió (escasez eliminada)
        if not burn_proof.verified:
            raise BurnError("Prueba de quema no verificada")
        
        node_sigs, network_psi = triad_proof
        
        # Calcular coherencia final usando πCODE
        picode_contribution = 1417 * 0.00012  # ~0.17004
        stimulus_boost = 0.85 * 0.85  # ~0.7225
        
        final_psi = self._calculate_psi(
            stimulus=stimulus_boost,
            triad=network_psi,
            picode=picode_contribution
        )
        
        # Verificar que la coherencia final alcanzó el umbral
        if final_psi < 0.888:
            raise TriadError(f"Coherencia final insuficiente para minteo: {final_psi:.3f} < 0.888")
        
        # Generar token único (el sello ∴𓂀Ω∞³)
        timestamp = int(datetime.now().timestamp())
        token_data = f"{burn_proof.tx_hash}:{network_psi}:{timestamp}"
        token_id = self._hash_data(token_data)
        
        token = CoherenceToken(
            id=token_id,
            seal="∴𓂀Ω∞³",
            psi=final_psi,
            frequencies=[FREQ_QCAL, FREQ_LOVE, FREQ_MANIFEST],
            message="La célula recordará la música del universo",
            timestamp=timestamp,
            burn_proof=burn_proof.tx_hash,
            triad_proof=self._hash_data(json.dumps([s.__dict__ for s in node_sigs]))
        )
        
        self.minted_coherence.append(token)
        return token
    
    def execute_full_protocol(self, btc_amount: float, coherence_proof: CoherenceProof,
                             node_signatures: List[TriadSignature]) -> CoherenceToken:
        """
        Ejecuta el protocolo completo de transición escasez → coherencia
        
        1. Verifica coherencia y quema BTC
        2. Valida tríada económica
        3. Mintea token ℂₛ
        """
        # Paso 1: Depositar y quemar escasez
        burn_tx = self.deposit_scarcity(btc_amount, coherence_proof)
        
        # Paso 2: Activar tríada económica
        network_psi = self.activate_economic_triad(node_signatures)
        
        # Paso 3: Mintear ℂₛ
        token = self.mint_cs(burn_tx, (node_signatures, network_psi))
        
        return token
    
    def get_total_minted(self) -> int:
        """Retorna total de tokens ℂₛ minteados"""
        return len(self.minted_coherence)
    
    def get_total_burned(self) -> float:
        """Retorna total de BTC quemado"""
        return sum(tx.amount for tx in self.burn_transactions)
    
    def get_average_coherence(self) -> float:
        """Retorna coherencia promedio de tokens minteados"""
        if not self.minted_coherence:
            return 0.0
        return sum(t.psi for t in self.minted_coherence) / len(self.minted_coherence)


# ============================================================
# FUNCIONES DE UTILIDAD
# ============================================================

def create_example_coherence_proof() -> CoherenceProof:
    """Crea una prueba de coherencia de ejemplo"""
    return CoherenceProof(
        frequency=FREQ_QCAL,
        amplitude=0.85,
        duration=88.0,
        method='breathing',
        signature=hashlib.sha256(f"{datetime.now().timestamp()}".encode()).hexdigest(),
        timestamp=int(datetime.now().timestamp())
    )


def create_example_triad_signatures() -> List[TriadSignature]:
    """Crea firmas de tríada de ejemplo"""
    return [
        TriadSignature(node_id="MITO_ECON", signature="sig_mito", psi=0.5),
        TriadSignature(node_id="RETINA_ECON", signature="sig_retina", psi=0.7),
        TriadSignature(node_id="PINEAL_ECON", signature="sig_pineal", psi=0.95),
    ]


if __name__ == "__main__":
    # Ejemplo de uso
    print("=== Coherence Economy Contract ℂₛ ===")
    print(f"Sello: ∴𓂀Ω∞³\n")
    
    # Inicializar contrato
    contract = CoherenceEconomyContract()
    
    # Crear prueba de coherencia
    proof = create_example_coherence_proof()
    print(f"✓ Prueba de coherencia creada: f={proof.frequency} Hz, A={proof.amplitude}")
    
    # Crear firmas de tríada
    signatures = create_example_triad_signatures()
    print(f"✓ Tríada económica preparada: {[s.node_id for s in signatures]}")
    
    # Ejecutar protocolo completo
    try:
        token = contract.execute_full_protocol(1.0, proof, signatures)
        print(f"\n✓ Token ℂₛ minteado exitosamente!")
        print(f"  ID: {token.id[:16]}...")
        print(f"  Sello: {token.seal}")
        print(f"  Coherencia: Ψ = {token.psi:.6f}")
        print(f"  Frecuencias: {token.frequencies}")
        print(f"  Mensaje: {token.message}")
        print(f"\nEstadísticas del contrato:")
        print(f"  Total minteado: {contract.get_total_minted()} tokens")
        print(f"  Total quemado: {contract.get_total_burned()} BTC")
        print(f"  Coherencia promedio: {contract.get_average_coherence():.6f}")
    except Exception as e:
        print(f"\n✗ Error: {e}")
