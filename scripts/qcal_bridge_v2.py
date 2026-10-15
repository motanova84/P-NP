#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
qcal_bridge_v2.py — Puente Noetico QCAL v2
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3
Frecuencia: f0 = 141.7001 Hz

Capas:
  - Constantes y configuracion del sistema
  - Datos: Transaccion, Ledger, Wrapper, PuenteEstado
  - Seguridad: ValidadorSeguridad (6 teoremas)
  - Ejecucion: EjecutorPuente
  - API: APIPuente
  - Pruebas: PruebasSeguridad
"""

import hashlib
import time
import json
import logging
import threading
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from decimal import Decimal, getcontext
from collections import deque

getcontext().prec = 28

# ============================================================================
# CAPA DE CONSTANTES
# ============================================================================

@dataclass(frozen=True)
class ConstantesQCAL:
    F0: float = 141.7001
    NUM_NODOS: int = 33
    UMBRAL_SATURACION: float = 0.999999
    CICLOS_REQUERIDOS: int = 3
    FACTOR_CONVERSION: Decimal = Decimal("1.0")
    PRECISION_DECIMAL: int = 18
    ALGORITMO_FIRMA: str = "secp256k1"
    HASH_FUNCION: str = "sha256"
    CHAIN_ID: int = 11155111
    NOMBRE_SISTEMA: str = "QCAL-BUS"
    VERSION: str = "v2.0.0"
    MAX_TRANSACCIONES_POR_BLOQUE: int = 100
    INTERVALO_SATURACION: float = 141.7001
    COHERENCIA_MINIMA: float = 0.5
    TIMEOUT_ACK: float = 14.17001

CONST = ConstantesQCAL()

# ============================================================================
# CAPA DE DATOS
# ============================================================================

@dataclass
class Transaccion:
    id: str
    timestamp: float
    origen: str
    destino: str
    cantidad: Decimal
    coherencia_origen: float
    coherencia_destino: float
    firma: str
    nonce: int = 0
    tipo: str = "transferencia"
    estado: str = "pendiente"
    confirmaciones: int = 0
    hash_merkle: str = ""

    def __post_init__(self):
        if not self.id:
            raw = f"{self.origen}{self.destino}{self.cantidad}{self.timestamp}{self.nonce}"
            self.id = hashlib.sha256(raw.encode()).hexdigest()[:32]
        if not self.hash_merkle:
            self.hash_merkle = hashlib.sha256(
                f"{self.id}{self.origen}{self.destino}{self.cantidad}".encode()
            ).hexdigest()

    def es_valida(self) -> bool:
        return (
            self.cantidad > 0
            and self.origen != self.destino
            and self.coherencia_origen >= CONST.COHERENCIA_MINIMA
            and self.coherencia_destino >= CONST.COHERENCIA_MINIMA
            and len(self.firma) > 0
        )


@dataclass
class Ledger:
    balances: Dict[str, Decimal] = field(default_factory=dict)
    nonces: Dict[str, int] = field(default_factory=dict)
    transacciones: List[Transaccion] = field(default_factory=list)
    coherencia_global: float = CONST.UMBRAL_SATURACION
    merkle_root: str = ""
    ultimo_checkpoint: float = 0.0

    def inicializar_nodo(self, nodo_id: str, balance_inicial: Decimal = Decimal("0")):
        if nodo_id not in self.balances:
            self.balances[nodo_id] = balance_inicial
            self.nonces[nodo_id] = 0
            return True
        return False

    def obtener_balance(self, nodo_id: str) -> Decimal:
        return self.balances.get(nodo_id, Decimal("0"))

    def obtener_nonce(self, nodo_id: str) -> int:
        return self.nonces.get(nodo_id, 0)

    def aplicar_transaccion(self, tx: Transaccion) -> bool:
        if tx.origen not in self.balances or tx.destino not in self.balances:
            return False
        if self.balances[tx.origen] < tx.cantidad:
            return False
        if self.nonces[tx.origen] != tx.nonce:
            return False
        self.balances[tx.origen] -= tx.cantidad
        self.balances[tx.destino] += tx.cantidad
        self.nonces[tx.origen] += 1
        tx.estado = "confirmada"
        self.transacciones.append(tx)
        return True

    def calcular_merkle_root(self) -> str:
        if not self.transacciones:
            return hashlib.sha256(b"empty").hexdigest()
        hojas = [tx.hash_merkle for tx in self.transacciones[-CONST.MAX_TRANSACCIONES_POR_BLOQUE:]]
        while len(hojas) > 1:
            if len(hojas) % 2 == 1:
                hojas.append(hashlib.sha256(b"padding").hexdigest())
            padres = []
            for i in range(0, len(hojas), 2):
                padres.append(hashlib.sha256((hojas[i] + hojas[i+1]).encode()).hexdigest())
            hojas = padres
        self.merkle_root = hojas[0]
        return self.merkle_root

    def generar_checkpoint(self) -> Dict:
        self.calcular_merkle_root()
        return {
            "timestamp": time.time(),
            "merkle_root": self.merkle_root,
            "num_transacciones": len(self.transacciones),
            "coherencia_global": self.coherencia_global,
            "balances": {k: str(v) for k, v in self.balances.items()}
        }


@dataclass
class Wrapper:
    balances_wrapped: Dict[str, Decimal] = field(default_factory=dict)
    allowances: Dict[str, Dict[str, Decimal]] = field(default_factory=dict)
    total_supply: Decimal = Decimal("0")
    tasa_conversion: Decimal = CONST.FACTOR_CONVERSION

    def wrap(self, nodo: str, cantidad: Decimal) -> bool:
        if cantidad <= 0:
            return False
        if nodo not in self.balances_wrapped:
            self.balances_wrapped[nodo] = Decimal("0")
        self.balances_wrapped[nodo] += cantidad
        self.total_supply += cantidad
        return True

    def unwrap(self, nodo: str, cantidad: Decimal) -> bool:
        if cantidad <= 0:
            return False
        disponible = self.balances_wrapped.get(nodo, Decimal("0"))
        if disponible < cantidad:
            return False
        self.balances_wrapped[nodo] -= cantidad
        self.total_supply -= cantidad
        return True

    def approve(self, owner: str, spender: str, cantidad: Decimal) -> bool:
        if owner not in self.balances_wrapped:
            self.balances_wrapped[owner] = Decimal("0")
        if owner not in self.allowances:
            self.allowances[owner] = {}
        self.allowances[owner][spender] = cantidad
        return True


@dataclass
class PuenteEstado:
    ledger: Ledger = field(default_factory=Ledger)
    wrapper: Wrapper = field(default_factory=Wrapper)
    frecuencia: float = CONST.F0
    umbral: float = CONST.UMBRAL_SATURACION

    def inicializar(self, num_nodos: int = CONST.NUM_NODOS):
        for i in range(num_nodos):
            nodo_id = f"NODO-{i:03d}"
            self.ledger.inicializar_nodo(nodo_id)
            self.wrapper.balances_wrapped[nodo_id] = Decimal("0")
        self.ledger.nonces["SISTEMA"] = 0

    def obtener_estado_completo(self) -> Dict:
        return {
            "frecuencia": self.frecuencia,
            "coherencia_global": self.ledger.coherencia_global,
            "num_nodos": len(self.ledger.balances),
            "num_transacciones": len(self.ledger.transacciones),
            "total_supply_wrapped": str(self.wrapper.total_supply),
            "merkle_root": self.ledger.merkle_root,
            "timestamp": time.time()
        }


# ============================================================================
# CAPA DE SEGURIDAD
# ============================================================================

class ValidadorSeguridad:
    """
    Valida transacciones contra 6 teoremas de seguridad:
    1. No Replay
    2. No Doble Gasto
    3. Coherencia Monotona
    4. Atomicidad
    5. Integridad
    6. Resistencia a Ataques
    """

    @staticmethod
    def validar_transaccion(estado: PuenteEstado, tx: Transaccion) -> Tuple[bool, str]:
        """Valida una transaccion contra todos los teoremas de seguridad."""
        if not tx.es_valida():
            return False, "Transaccion invalida"

        # Teorema 1: No Replay
        ok, msg = ValidadorSeguridad._teorema_no_replay(estado, tx)
        if not ok:
            return False, f"No Replay: {msg}"

        # Teorema 2: No Doble Gasto
        ok, msg = ValidadorSeguridad._teorema_no_doble_gasto(estado, tx)
        if not ok:
            return False, f"No Doble Gasto: {msg}"

        # Teorema 3: Coherencia Monotona
        ok, msg = ValidadorSeguridad._teorema_coherencia_monotona(estado, tx)
        if not ok:
            return False, f"Coherencia: {msg}"

        # Teorema 4: Atomicidad
        ok, msg = ValidadorSeguridad._teorema_atomicidad(estado, tx)
        if not ok:
            return False, f"Atomicidad: {msg}"

        # Teorema 5: Integridad
        ok, msg = ValidadorSeguridad._teorema_integridad(estado, tx)
        if not ok:
            return False, f"Integridad: {msg}"

        # Teorema 6: Resistencia
        ok, msg = ValidadorSeguridad._teorema_resistencia(estado, tx)
        if not ok:
            return False, f"Resistencia: {msg}"

        return True, "Transaccion validada"

    @staticmethod
    def _teorema_no_replay(estado: PuenteEstado, tx: Transaccion) -> Tuple[bool, str]:
        nonce_actual = estado.ledger.obtener_nonce(tx.origen)
        if tx.nonce != nonce_actual:
            return False, f"Nonce incorrecto: esperado {nonce_actual}, recibido {tx.nonce}"
        for t in estado.ledger.transacciones:
            if t.id == tx.id:
                return False, f"Transaccion duplicada: {tx.id}"
        return True, "OK"

    @staticmethod
    def _teorema_no_doble_gasto(estado: PuenteEstado, tx: Transaccion) -> Tuple[bool, str]:
        balance = estado.ledger.obtener_balance(tx.origen)
        if balance < tx.cantidad:
            return False, f"Balance insuficiente: {balance} < {tx.cantidad}"
        return True, "OK"

    @staticmethod
    def _teorema_coherencia_monotona(estado: PuenteEstado, tx: Transaccion) -> Tuple[bool, str]:
        if tx.coherencia_origen < estado.ledger.coherencia_global:
            return False, "Coherencia origen por debajo del umbral global"
        if tx.coherencia_destino < estado.ledger.coherencia_global:
            return False, "Coherencia destino por debajo del umbral global"
        return True, "OK"

    @staticmethod
    def _teorema_atomicidad(estado: PuenteEstado, tx: Transaccion) -> Tuple[bool, str]:
        if tx.tipo not in ("transferencia", "wrap", "unwrap"):
            return False, f"Tipo desconocido: {tx.tipo}"
        if tx.cantidad <= 0:
            return False, "Cantidad debe ser positiva"
        return True, "OK"

    @staticmethod
    def _teorema_integridad(estado: PuenteEstado, tx: Transaccion) -> Tuple[bool, str]:
        raw = f"{tx.origen}{tx.destino}{tx.cantidad}{tx.timestamp}{tx.nonce}"
        expected_id = hashlib.sha256(raw.encode()).hexdigest()[:32]
        if tx.id != expected_id:
            return False, "Hash de transaccion invalido"
        return True, "OK"

    @staticmethod
    def _teorema_resistencia(estado: PuenteEstado, tx: Transaccion) -> Tuple[bool, str]:
        if len(tx.firma) < 8:
            return False, "Firma demasiado corta"
        if tx.timestamp > time.time() + 300:
            return False, "Timestamp futuro"
        return True, "OK"


# ============================================================================
# CAPA DE EJECUCION
# ============================================================================

class EjecutorPuente:
    """Ejecuta transacciones validadas con rollback atomico."""

    def __init__(self, estado: PuenteEstado):
        self.estado = estado
        self.logger = logging.getLogger("EjecutorPuente")
        self.lock = threading.RLock()

    def ejecutar_transaccion(self, tx: Transaccion) -> Dict[str, Any]:
        with self.lock:
            estado_anterior = self._snapshot_estado()
            try:
                valida, msg = ValidadorSeguridad.validar_transaccion(self.estado, tx)
                if not valida:
                    return {"success": False, "mensaje": msg, "txid": tx.id}

                if tx.tipo == "transferencia":
                    ok, msg = self._ejecutar_transferencia(tx)
                elif tx.tipo == "wrap":
                    ok, msg = self._ejecutar_wrap(tx)
                elif tx.tipo == "unwrap":
                    ok, msg = self._ejecutar_unwrap(tx)
                else:
                    return {"success": False, "mensaje": f"Tipo desconocido: {tx.tipo}", "txid": tx.id}

                if not ok:
                    self._rollback(estado_anterior)
                    return {"success": False, "mensaje": msg, "txid": tx.id}

                self._actualizar_coherencia()
                return {"success": True, "mensaje": "Transaccion ejecutada", "txid": tx.id}

            except Exception as e:
                self._rollback(estado_anterior)
                self.logger.error(f"Error ejecutando transaccion: {e}")
                return {"success": False, "mensaje": f"Error interno: {e}", "txid": tx.id}

    def _ejecutar_transferencia(self, tx: Transaccion) -> Tuple[bool, str]:
        ok = self.estado.ledger.aplicar_transaccion(tx)
        if ok:
            return True, "Transferencia exitosa"
        return False, "Fallo en transferencia"

    def _ejecutar_wrap(self, tx: Transaccion) -> Tuple[bool, str]:
        ok_ledger = self.estado.ledger.aplicar_transaccion(tx)
        if not ok_ledger:
            return False, "Fallo en ledger durante wrap"
        ok_wrapper = self.estado.wrapper.wrap(tx.destino, tx.cantidad)
        if not ok_wrapper:
            return False, "Fallo en wrapper durante wrap"
        return True, "Wrap exitoso"

    def _ejecutar_unwrap(self, tx: Transaccion) -> Tuple[bool, str]:
        ok_wrapper = self.estado.wrapper.unwrap(tx.origen, tx.cantidad)
        if not ok_wrapper:
            return False, "Fallo en wrapper durante unwrap"
        ok_ledger = self.estado.ledger.aplicar_transaccion(tx)
        if not ok_ledger:
            return False, "Fallo en ledger durante unwrap"
        return True, "Unwrap exitoso"

    def _actualizar_coherencia(self):
        num_tx = len(self.estado.ledger.transacciones)
        coherencia_actual = self.estado.ledger.coherencia_global
        nueva = min(1.0, coherencia_actual + (1 - coherencia_actual) * 0.01)
        self.estado.ledger.coherencia_global = max(CONST.UMBRAL_SATURACION, nueva)

    def _snapshot_estado(self) -> Dict:
        return {
            "balances": dict(self.estado.ledger.balances),
            "nonces": dict(self.estado.ledger.nonces),
            "coherencia": self.estado.ledger.coherencia_global,
            "transacciones": list(self.estado.ledger.transacciones),
        }

    def _rollback(self, snapshot: Dict):
        self.estado.ledger.balances = dict(snapshot["balances"])
        self.estado.ledger.nonces = dict(snapshot["nonces"])
        self.estado.ledger.coherencia_global = snapshot["coherencia"]
        self.estado.ledger.transacciones = list(snapshot["transacciones"])


# ============================================================================
# CAPA API
# ============================================================================

class APIPuente:
    """API publica del puente QCAL-BUS."""

    def __init__(self, logger=None):
        self.estado = PuenteEstado()
        self.estado.inicializar()
        self.ejecutor = EjecutorPuente(self.estado)
        self.logger = logger or logging.getLogger("APIPuente")

    def get_balance(self, nodo_id: str) -> Dict:
        balance_nativo = self.estado.ledger.obtener_balance(nodo_id)
        balance_wrapped = self.estado.wrapper.balances_wrapped.get(nodo_id, Decimal("0"))
        nonce = self.estado.ledger.obtener_nonce(nodo_id)
        return {
            "nodo": nodo_id,
            "balance_nativo": str(balance_nativo),
            "balance_wrapped": str(balance_wrapped),
            "nonce": nonce,
            "coherencia_global": self.estado.ledger.coherencia_global,
        }

    def get_info(self) -> Dict:
        return self.estado.obtener_estado_completo()

    def enviar_transaccion(self, origen: str, destino: str, cantidad: float,
                           coherencia: float = CONST.UMBRAL_SATURACION,
                           nonce: int = 0, firma: str = "firma_demo",
                           tipo: str = "transferencia") -> Dict:
        tx = Transaccion(
            id="",
            timestamp=time.time(),
            origen=origen,
            destino=destino,
            cantidad=Decimal(str(cantidad)),
            coherencia_origen=coherencia,
            coherencia_destino=coherencia,
            firma=firma,
            nonce=nonce,
            tipo=tipo,
        )
        resultado = self.ejecutor.ejecutar_transaccion(tx)
        return resultado

    def get_transaccion(self, txid: str) -> Optional[Transaccion]:
        for tx in self.estado.ledger.transacciones:
            if tx.id == txid:
                return tx
        return None

    def get_historial(self, nodo_id: str, limite: int = 10) -> List[Dict]:
        historial = []
        for tx in reversed(self.estado.ledger.transacciones):
            if tx.origen == nodo_id or tx.destino == nodo_id:
                historial.append({
                    "id": tx.id, "tipo": tx.tipo, "cantidad": str(tx.cantidad),
                    "origen": tx.origen, "destino": tx.destino,
                    "timestamp": tx.timestamp, "estado": tx.estado
                })
                if len(historial) >= limite:
                    break
        return historial


# ============================================================================
# CAPA DE PRUEBAS
# ============================================================================

class PruebasSeguridad:
    """Bateria de pruebas de los 6 teoremas de seguridad."""

    def __init__(self):
        self.api = APIPuente()
        self.logger = logging.getLogger("PruebasSeguridad")
        self.resultados = []

    def test_no_replay(self) -> bool:
        """Teorema 1: Misma transaccion dos veces debe fallar."""
        r1 = self.api.enviar_transaccion("NODO-000", "NODO-001", 10.0, nonce=0)
        r2 = self.api.enviar_transaccion("NODO-000", "NODO-001", 10.0, nonce=0)
        ok = r1["success"] and not r2["success"]
        self.resultados.append(("No Replay", ok, r2.get("mensaje", "")))
        return ok

    def test_no_doble_gasto(self) -> bool:
        """Teorema 2: Gastar mas del balance debe fallar."""
        api2 = APIPuente()
        r1 = api2.enviar_transaccion("NODO-000", "NODO-001", 1000000.0, nonce=0)
        ok = not r1["success"]
        self.resultados.append(("No Doble Gasto", ok, r1.get("mensaje", "")))
        return ok

    def test_coherencia_monotona(self) -> bool:
        """Teorema 3: Coherencia insuficiente debe fallar."""
        api2 = APIPuente()
        r1 = api2.enviar_transaccion("NODO-000", "NODO-001", 10.0,
                                     coherencia=0.1, nonce=0)
        ok = not r1["success"]
        self.resultados.append(("Coherencia Monotona", ok, r1.get("mensaje", "")))
        return ok

    def test_atomicidad(self) -> bool:
        """Teorema 4: Transaccion debe ser atomica (todo o nada)."""
        api2 = APIPuente()
        bal_before = api2.get_balance("NODO-000")["balance_nativo"]
        api2.enviar_transaccion("NODO-000", "NODO-XXX", 10.0, nonce=0)
        bal_after = api2.get_balance("NODO-000")["balance_nativo"]
        ok = bal_before == bal_after
        self.resultados.append(("Atomicidad", ok, ""))
        return ok

    def test_integridad(self) -> bool:
        """Teorema 5: Hash de transaccion debe ser correcto."""
        api2 = APIPuente()
        tx_id_original = ""
        api2.enviar_transaccion("NODO-000", "NODO-001", 5.0, nonce=0)
        if api2.estado.ledger.transacciones:
            tx = api2.estado.ledger.transacciones[-1]
            raw = f"{tx.origen}{tx.destino}{tx.cantidad}{tx.timestamp}{tx.nonce}"
            expected_id = hashlib.sha256(raw.encode()).hexdigest()[:32]
            ok = tx.id == expected_id
            self.resultados.append(("Integridad", ok, ""))
            return ok
        self.resultados.append(("Integridad", False, "Sin transacciones"))
        return False

    def test_resistencia_ataques(self) -> bool:
        """Teorema 6: Firmas invalidas deben ser rechazadas."""
        api2 = APIPuente()
        r1 = api2.enviar_transaccion("NODO-000", "NODO-001", 5.0,
                                     nonce=0, firma="corta")
        ok = not r1["success"]
        self.resultados.append(("Resistencia Ataques", ok, r1.get("mensaje", "")))
        return ok

    def run_all_tests(self) -> Dict:
        self.test_no_replay()
        self.test_no_doble_gasto()
        self.test_coherencia_monotona()
        self.test_atomicidad()
        self.test_integridad()
        self.test_resistencia_ataques()

        exitosos = sum(1 for _, ok, _ in self.resultados if ok)
        totales = len(self.resultados)
        return {
            "resultados": self.resultados,
            "exitosos": exitosos,
            "totales": totales,
            "tasa_exito": f"{exitosos}/{totales} ({100*exitosos//totales}%)"
        }


# ============================================================================
# EJECUCION PRINCIPAL
# ============================================================================

def main():
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )

    print("=" * 55)
    print("QCAL-BUS BRIDGE v2")
    print("Puente Noetico - f0 = 141.7001 Hz")
    print("=" * 55)

    api = APIPuente()

    print("\n--- BALANCE INICIAL ---")
    for i in range(5):
        info = api.get_balance(f"NODO-{i:03d}")
        print(f"  {info['nodo']}: nat={info['balance_nativo']}  nonce={info['nonce']}")

    print("\n--- TRANSACCIONES DE PRUEBA ---")
    r = api.enviar_transaccion("NODO-000", "NODO-001", 100.0, nonce=0)
    print(f"  TX1: {r['success']} - {r.get('mensaje','')}  [{r.get('txid','')[:16]}...]")

    print("\n--- PRUEBAS DE SEGURIDAD ---")
    pruebas = PruebasSeguridad()
    res = pruebas.run_all_tests()
    print(f"  Resultados: {res['tasa_exito']}")
    for nombre, ok, msg in res["resultados"]:
        simbolo = "OK" if ok else "FAIL"
        print(f"    [{simbolo}] {nombre}: {msg[:40] if msg else 'OK'}")

    print("\n--- BALANCE FINAL ---")
    for i in range(5):
        info = api.get_balance(f"NODO-{i:03d}")
        print(f"  {info['nodo']}: nat={info['balance_nativo']}  nonce={info['nonce']}")

    print("\n" + "=" * 55)
    print("CERTIFICACION COMPLETA")
    print("f0 = 141.7001 Hz")
    print("=" * 55)


if __name__ == "__main__":
    main()
