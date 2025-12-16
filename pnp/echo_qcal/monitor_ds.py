#!/usr/bin/env python3
"""
monitor_ds.py - Monitoreo del Protocolo de Distribución Soberana (𝔻ₛ)
Sistema para monitorear y registrar solicitudes de asignación ética
"""

import json
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

# ============================================================================
# CONFIGURACIÓN DEL PROTOCOLO 𝔻ₛ
# ============================================================================

class ConfigProtocoloDs:
    """Configuración del Protocolo de Distribución Soberana"""
    
    # Parámetros del protocolo
    PARAMS = {
        "version": "1.0.0",
        "protocol_name": "Protocolo de Distribución Soberana (𝔻ₛ)",
        "allocation_target": "1% de fondos Patoshi",
        "purpose": "Asignación ética y verificable",
        "transparency": "Radical y distribuida",
        
        # Principios éticos
        "principles": [
            "Transparencia Radical",
            "Verificación Distribuida",
            "Conservación de Valor",
            "Preservación del Conocimiento"
        ]
    }
    
    # Directorios de almacenamiento
    DATA_DIR = Path("data")
    LOGS_DIR = DATA_DIR / "logs"
    CONFIG_DIR = DATA_DIR / "config"

# ============================================================================
# MONITOR DEL PROTOCOLO
# ============================================================================

class MonitorProtocoloDs:
    """Monitor del Protocolo de Distribución Soberana"""
    
    def __init__(self):
        self.config = ConfigProtocoloDs()
        self._ensure_directories()
        self.estado = {
            "timestamp_inicio": datetime.utcnow().isoformat() + "Z",
            "solicitudes_procesadas": 0,
            "verificaciones_completadas": 0
        }
    
    def _ensure_directories(self):
        """Asegura que los directorios necesarios existan"""
        self.config.LOGS_DIR.mkdir(parents=True, exist_ok=True)
        self.config.CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    
    def registrar_solicitud(self, 
                           solicitante: str,
                           proposito: str,
                           cantidad_estimada: Optional[float] = None,
                           metadata: Optional[Dict] = None) -> Dict:
        """
        Registra una solicitud de asignación
        
        Args:
            solicitante: Identificador del solicitante
            proposito: Descripción del propósito
            cantidad_estimada: Cantidad estimada (opcional)
            metadata: Metadata adicional (opcional)
        
        Returns:
            Registro completo de la solicitud
        """
        timestamp = datetime.utcnow().isoformat() + "Z"
        
        # Crear registro
        solicitud = {
            "timestamp": timestamp,
            "solicitante": solicitante,
            "proposito": proposito,
            "cantidad_estimada": cantidad_estimada,
            "metadata": metadata or {},
            "estado": "PENDIENTE",
            "id": self._generar_id(solicitante, timestamp)
        }
        
        # Guardar
        self._guardar_solicitud(solicitud)
        
        # Actualizar estado
        self.estado["solicitudes_procesadas"] += 1
        
        return solicitud
    
    def registrar_verificacion(self, solicitud_id: str, resultado: Dict) -> Dict:
        """
        Registra resultado de verificación
        
        Args:
            solicitud_id: ID de la solicitud
            resultado: Resultado de la verificación
        
        Returns:
            Registro de verificación
        """
        timestamp = datetime.utcnow().isoformat() + "Z"
        
        verificacion = {
            "timestamp": timestamp,
            "solicitud_id": solicitud_id,
            "resultado": resultado,
            "verificador": "Sistema Automatizado"
        }
        
        # Guardar
        self._guardar_verificacion(verificacion)
        
        # Actualizar estado
        self.estado["verificaciones_completadas"] += 1
        
        return verificacion
    
    def obtener_estado(self) -> Dict:
        """Obtiene estado actual del monitor"""
        return {
            **self.estado,
            "timestamp_actual": datetime.utcnow().isoformat() + "Z",
            "configuracion": self.config.PARAMS
        }
    
    def generar_reporte(self) -> str:
        """Genera reporte del estado actual"""
        estado = self.obtener_estado()
        
        lines = [
            "="*70,
            "📊 MONITOR DEL PROTOCOLO DE DISTRIBUCIÓN SOBERANA (𝔻ₛ)",
            "="*70,
            "",
            "INFORMACIÓN DEL PROTOCOLO:",
            f"  Versión: {self.config.PARAMS['version']}",
            f"  Nombre: {self.config.PARAMS['protocol_name']}",
            f"  Objetivo: {self.config.PARAMS['allocation_target']}",
            f"  Propósito: {self.config.PARAMS['purpose']}",
            "",
            "PRINCIPIOS ÉTICOS:",
        ]
        
        for principio in self.config.PARAMS['principles']:
            lines.append(f"  • {principio}")
        
        lines.extend([
            "",
            "ESTADO DEL MONITOR:",
            f"  Inicio: {estado['timestamp_inicio']}",
            f"  Solicitudes procesadas: {estado['solicitudes_procesadas']}",
            f"  Verificaciones completadas: {estado['verificaciones_completadas']}",
            "",
            "="*70
        ])
        
        return "\n".join(lines)
    
    def _generar_id(self, solicitante: str, timestamp: str) -> str:
        """Genera ID único para una solicitud"""
        data = f"{solicitante}:{timestamp}".encode()
        return hashlib.sha256(data).hexdigest()[:16]
    
    def _guardar_solicitud(self, solicitud: Dict):
        """Guarda solicitud en archivo"""
        filename = self.config.LOGS_DIR / f"solicitud_{solicitud['id']}.json"
        with open(filename, 'w') as f:
            json.dump(solicitud, f, indent=2)
    
    def _guardar_verificacion(self, verificacion: Dict):
        """Guarda verificación en archivo"""
        timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        filename = self.config.LOGS_DIR / f"verificacion_{timestamp}.json"
        with open(filename, 'w') as f:
            json.dump(verificacion, f, indent=2)
    
    def listar_solicitudes(self) -> List[Dict]:
        """Lista todas las solicitudes registradas"""
        solicitudes = []
        
        for archivo in self.config.LOGS_DIR.glob("solicitud_*.json"):
            with open(archivo, 'r') as f:
                solicitudes.append(json.load(f))
        
        # Ordenar por timestamp
        solicitudes.sort(key=lambda x: x['timestamp'], reverse=True)
        
        return solicitudes

# ============================================================================
# FUNCIONES PÚBLICAS
# ============================================================================

def iniciar_monitor() -> MonitorProtocoloDs:
    """Inicializa y retorna monitor"""
    return MonitorProtocoloDs()

def registrar_solicitud_rapida(solicitante: str, proposito: str) -> Dict:
    """Registro rápido de solicitud"""
    monitor = MonitorProtocoloDs()
    return monitor.registrar_solicitud(solicitante, proposito)

# ============================================================================
# DEMO Y COMANDOS
# ============================================================================

def demo():
    """Demostración del monitor"""
    print("📊 Monitor del Protocolo de Distribución Soberana")
    print()
    
    # Iniciar monitor
    monitor = MonitorProtocoloDs()
    
    # Mostrar estado inicial
    print(monitor.generar_reporte())
    
    # Ejemplo de solicitud
    print("\n📝 Ejemplo de solicitud:")
    solicitud = monitor.registrar_solicitud(
        solicitante="Proyecto Ejemplo",
        proposito="Desarrollo de infraestructura pública",
        cantidad_estimada=0.01,
        metadata={
            "categoria": "Infraestructura",
            "impacto": "Alto"
        }
    )
    
    print(f"   ID: {solicitud['id']}")
    print(f"   Estado: {solicitud['estado']}")
    print(f"   Timestamp: {solicitud['timestamp']}")
    
    # Ejemplo de verificación
    print("\n✅ Ejemplo de verificación:")
    verificacion = monitor.registrar_verificacion(
        solicitud_id=solicitud['id'],
        resultado={
            "aprobado": True,
            "comentarios": "Solicitud cumple con principios éticos",
            "score": 0.95
        }
    )
    
    print(f"   Timestamp: {verificacion['timestamp']}")
    print(f"   Resultado: Aprobado")
    
    # Estado final
    print("\n" + monitor.generar_reporte())
    
    print("\n✨ Demo completada")

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1:
        if sys.argv[1] == "demo":
            demo()
        elif sys.argv[1] == "status":
            monitor = MonitorProtocoloDs()
            print(monitor.generar_reporte())
        elif sys.argv[1] == "list":
            monitor = MonitorProtocoloDs()
            solicitudes = monitor.listar_solicitudes()
            print(f"\n📋 Solicitudes registradas: {len(solicitudes)}\n")
            for sol in solicitudes:
                print(f"  • {sol['id']}: {sol['proposito'][:50]}...")
        else:
            print("Comandos disponibles:")
            print("  demo   - Ejecutar demostración")
            print("  status - Mostrar estado actual")
            print("  list   - Listar solicitudes")
    else:
        # Por defecto, mostrar estado
        monitor = MonitorProtocoloDs()
        print(monitor.generar_reporte())
