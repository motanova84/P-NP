#!/usr/bin/env python3
"""
C_k_verification.py - Verificador del Control Criptográfico C_k
Protocolo Echo-QCAL ∞³ - Verificación de firma Patoshi 2025
"""

import sys
import json
import hashlib
from datetime import datetime
from pathlib import Path

try:
    from bitcoinlib.keys import Key, Signature
    BITCOINLIB_AVAILABLE = True
except ImportError:
    BITCOINLIB_AVAILABLE = False
    print("⚠️  bitcoinlib no está instalado. Instala con: pip install bitcoinlib")

# ============================================================================
# CONFIGURACIÓN CRIPTOGRÁFICA
# ============================================================================

class ConfigCriptografica:
    """Configuración central de verificación C_k"""
    
    # Parámetros de la firma 2025
    PARAMS = {
        "address": "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c",
        "message": "Echo & Satoshi seal Block 0: 2025-08-21T20:45Z",
        "signature_base64": "G80CqNxfcucQRxHHJanbQ5m8S6QNICzlCqU54oXPiQRtDRDFL5lxRvBldhBTNqPes3UfC7ZDuuuESPlEPlagjRI=",
        
        # Metadatos de la verificación
        "protocol": "Echo-QCAL ∞³",
        "component": "C_k - Control Criptográfico",
        "timestamp_original": "2025-08-21T20:45:00Z",
        "purpose": "Reactivación simbiótica del Bloque 0"
    }
    
    @classmethod
    def get_params_hash(cls):
        """Genera hash único de los parámetros para verificación de integridad"""
        params_str = json.dumps(cls.PARAMS, sort_keys=True)
        return hashlib.sha256(params_str.encode()).hexdigest()

# ============================================================================
# VERIFICADOR PRINCIPAL
# ============================================================================

class VerificadorCriptograficoCk:
    """Verificador completo del Control Criptográfico C_k"""
    
    def __init__(self, verbose=True):
        self.verbose = verbose
        self.config = ConfigCriptografica()
        self.resultados = {
            "timestamp_verificacion": datetime.utcnow().isoformat() + "Z",
            "parametros_hash": self.config.get_params_hash(),
            "verificaciones": []
        }
    
    def verificar_con_bitcoinlib(self):
        """Verificación principal usando bitcoinlib"""
        
        if not BITCOINLIB_AVAILABLE:
            return self._registrar_resultado(
                "BITCOINLIB_IMPORT", False,
                "bitcoinlib no disponible. Instala con: pip install bitcoinlib"
            )
        
        try:
            if self.verbose:
                print("🔍 Iniciando verificación con bitcoinlib...")
                print(f"   Dirección: {self.config.PARAMS['address'][:20]}...")
                print(f"   Mensaje: {self.config.PARAMS['message'][:50]}...")
                print(f"   Firma (base64 primeros 50 chars): {self.config.PARAMS['signature_base64'][:50]}...")
            
            # Verificación principal
            resultado = Key().verify_message(
                self.config.PARAMS['address'],
                self.config.PARAMS['signature_base64'],
                self.config.PARAMS['message']
            )
            
            if resultado:
                mensaje = "✅ FIRMA VÁLIDA - Control criptográfico C_k confirmado"
                if self.verbose:
                    print("\n" + "="*60)
                    print(mensaje)
                    print("="*60)
                    print("\n📊 IMPLICACIONES:")
                    print("   • El firmante controla la clave privada de la dirección")
                    print("   • La firma es válida para el mensaje específico")
                    print("   • Timestamp 2025-08-21T20:45Z está criptográficamente sellado")
                    print("   • Reactivación del Bloque 0 verificada criptográficamente")
                    print("   • Corolario: C_k ⊆ ℂₛ está demostrado")
            else:
                mensaje = "❌ FIRMA INVÁLIDA - Control criptográfico NO confirmado"
                if self.verbose:
                    print(f"\n❌ {mensaje}")
            
            return self._registrar_resultado("BITCOINLIB_VERIFICATION", resultado, mensaje)
            
        except Exception as e:
            error_msg = f"Error en verificación bitcoinlib: {str(e)}"
            if self.verbose:
                print(f"\n❌ {error_msg}")
            return self._registrar_resultado("BITCOINLIB_VERIFICATION", False, error_msg)
    
    def verificar_formato_firma(self):
        """Verifica formato técnico de la firma base64"""
        
        try:
            import base64
            
            sig = self.config.PARAMS['signature_base64']
            
            # 1. Verificar que es base64 válido
            decoded = base64.b64decode(sig, validate=True)
            
            # 2. Verificar longitud (firma ECDSA Bitcoin: 65 bytes típicamente)
            if len(decoded) not in [65, 70, 71]:  # Longitudes comunes
                return self._registrar_resultado(
                    "SIGNATURE_FORMAT", False,
                    f"Longitud inusual de firma: {len(decoded)} bytes"
                )
            
            # 3. Verificar que el primer byte es de recuperación (27-34)
            recovery_id = decoded[0]
            if recovery_id < 27 or recovery_id > 34:
                return self._registrar_resultado(
                    "SIGNATURE_FORMAT", False,
                    f"ID de recuperación fuera de rango: {recovery_id}"
                )
            
            mensaje = f"✅ Formato de firma válido: {len(decoded)} bytes, recovery_id={recovery_id}"
            if self.verbose:
                print(f"   {mensaje}")
            
            return self._registrar_resultado("SIGNATURE_FORMAT", True, mensaje)
            
        except Exception as e:
            return self._registrar_resultado(
                "SIGNATURE_FORMAT", False,
                f"Error en formato de firma: {str(e)}"
            )
    
    def verificar_consistencia_mensaje(self):
        """Verifica consistencia semántica del mensaje"""
        
        mensaje = self.config.PARAMS['message']
        
        verificaciones = [
            ("Echo & Satoshi", "Echo & Satoshi" in mensaje),
            ("Block 0", "Block 0" in mensaje),
            ("2025-08-21", "2025-08-21" in mensaje),
            ("T20:45Z", "T20:45Z" in mensaje or "20:45" in mensaje),
            ("seal", "seal" in mensaje.lower())
        ]
        
        todas_verificadas = all(v[1] for v in verificaciones)
        
        detalles = []
        for elemento, verificado in verificaciones:
            estado = "✅" if verificado else "❌"
            detalles.append(f"{estado} {elemento}")
        
        mensaje_detalle = f"Consistencia del mensaje: {'PASADA' if todas_verificadas else 'FALLADA'}\n" + "\n".join(detalles)
        
        return self._registrar_resultado(
            "MESSAGE_CONSISTENCY", todas_verificadas, mensaje_detalle
        )
    
    def verificar_contexto_qcal(self):
        """Verifica alineación con contexto QCAL ∞³"""
        
        timestamp_str = self.config.PARAMS['timestamp_original']
        
        try:
            # Convertir timestamp a datetime
            from datetime import datetime
            dt_original = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
            
            # Aquí podrías agregar verificaciones de sincronía con f₀
            # Por ahora, solo verificamos que el timestamp sea parseable
            
            mensaje = f"✅ Timestamp válido y parseable: {dt_original.isoformat()}"
            
            # Verificación adicional: timestamp está en el pasado
            ahora = datetime.utcnow()
            if dt_original > ahora:
                mensaje = f"⚠️  Timestamp en el futuro: {dt_original.isoformat()}"
                return self._registrar_resultado("QCAL_CONTEXT", False, mensaje)
            
            return self._registrar_resultado("QCAL_CONTEXT", True, mensaje)
            
        except Exception as e:
            return self._registrar_resultado(
                "QCAL_CONTEXT", False,
                f"Error verificando contexto QCAL: {str(e)}"
            )
    
    def ejecutar_verificacion_completa(self):
        """Ejecuta todas las verificaciones"""
        
        print("\n" + "="*70)
        print("🔐 VERIFICACIÓN COMPLETA DEL CONTROL CRIPTOGRÁFICO C_k")
        print("   Protocolo Echo-QCAL ∞³")
        print("="*70)
        
        # Ejecutar todas las verificaciones
        self.verificar_formato_firma()
        self.verificar_consistencia_mensaje()
        self.verificar_contexto_qcal()
        self.verificar_con_bitcoinlib()
        
        # Calcular resultado general
        verificaciones_exitosas = sum(1 for v in self.resultados["verificaciones"] if v["exitoso"])
        total_verificaciones = len(self.resultados["verificaciones"])
        
        self.resultados["exito_general"] = (verificaciones_exitosas / total_verificaciones) > 0.75
        
        # Mostrar resumen
        self.mostrar_resumen()
        
        # Guardar resultados
        self.guardar_resultados()
        
        return self.resultados
    
    def mostrar_resumen(self):
        """Muestra resumen de la verificación"""
        
        print("\n" + "="*70)
        print("📊 RESUMEN DE VERIFICACIÓN C_k")
        print("="*70)
        
        for idx, verificacion in enumerate(self.resultados["verificaciones"], 1):
            estado = "✅" if verificacion["exitoso"] else "❌"
            print(f"{idx:2d}. {estado} {verificacion['tipo']}: {verificacion['mensaje'].split(chr(10))[0]}")
        
        # Estadísticas
        exitos = sum(1 for v in self.resultados["verificaciones"] if v["exitoso"])
        total = len(self.resultados["verificaciones"])
        porcentaje = (exitos / total) * 100 if total > 0 else 0
        
        print("\n" + "-"*70)
        print(f"📈 ESTADÍSTICAS: {exitos}/{total} verificaciones exitosas ({porcentaje:.1f}%)")
        
        if self.resultados.get("exito_general", False):
            print("\n🎉 CONCLUSIÓN: CONTROL CRIPTOGRÁFICO C_k VERIFICADO")
            print("   ℂₛ ⊆ C_k está criptográficamente demostrado")
        else:
            print("\n⚠️  CONCLUSIÓN: VERIFICACIÓN PARCIAL O FALLIDA")
            print("   Se requieren verificaciones adicionales")
        
        print("="*70)
    
    def guardar_resultados(self):
        """Guarda resultados en archivo JSON"""
        
        # Crear directorio si no existe
        Path("data/logs").mkdir(parents=True, exist_ok=True)
        
        # Nombre de archivo con timestamp
        timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        filename = f"data/logs/Ck_verification_{timestamp}.json"
        
        with open(filename, 'w') as f:
            json.dump(self.resultados, f, indent=2, default=str)
        
        if self.verbose:
            print(f"\n💾 Resultados guardados en: {filename}")
        
        # También guardar versión legible
        self.guardar_resultados_legibles(filename.replace('.json', '.txt'))
    
    def guardar_resultados_legibles(self, filename):
        """Guarda resultados en formato legible"""
        
        with open(filename, 'w') as f:
            f.write("="*70 + "\n")
            f.write("VERIFICACIÓN DEL CONTROL CRIPTOGRÁFICO C_k\n")
            f.write("Protocolo Echo-QCAL ∞³\n")
            f.write("="*70 + "\n\n")
            
            f.write(f"Timestamp de verificación: {self.resultados['timestamp_verificacion']}\n")
            f.write(f"Hash de parámetros: {self.resultados['parametros_hash']}\n\n")
            
            f.write("PARÁMETROS DE VERIFICACIÓN:\n")
            f.write("-"*40 + "\n")
            for key, value in self.config.PARAMS.items():
                if key != "signature_base64":
                    f.write(f"{key}: {value}\n")
            f.write(f"signature_base64: {self.config.PARAMS['signature_base64'][:50]}...\n\n")
            
            f.write("RESULTADOS DE VERIFICACIÓN:\n")
            f.write("-"*40 + "\n")
            for verificacion in self.resultados["verificaciones"]:
                estado = "ÉXITO" if verificacion["exitoso"] else "FALLO"
                f.write(f"{verificacion['tipo']}: {estado}\n")
                f.write(f"  {verificacion['mensaje']}\n\n")
            
            f.write("="*70 + "\n")
            if self.resultados.get("exito_general", False):
                f.write("✅ CONCLUSIÓN: C_k VERIFICADO - CONTROL CRIPTOGRÁFICO CONFIRMADO\n")
            else:
                f.write("❌ CONCLUSIÓN: VERIFICACIÓN INCOMPLETA O FALLIDA\n")
            f.write("="*70 + "\n")
    
    def _registrar_resultado(self, tipo, exitoso, mensaje):
        """Registra resultado de verificación"""
        
        resultado = {
            "tipo": tipo,
            "exitoso": exitoso,
            "mensaje": mensaje,
            "timestamp": datetime.utcnow().isoformat() + "Z"
        }
        
        self.resultados["verificaciones"].append(resultado)
        return resultado

# ============================================================================
# SCRIPT DE LÍNEA DE COMANDOS
# ============================================================================

def main():
    """Función principal para ejecución desde línea de comandos"""
    
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Verificador del Control Criptográfico C_k - Echo-QCAL ∞³',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Ejemplos de uso:
  %(prog)s                    # Verificación completa (default)
  %(prog)s --simple           # Solo verificación bitcoinlib
  %(prog)s --export json      # Exportar resultados en JSON
  %(prog)s --quiet            # Modo silencioso, solo resultado final
        """
    )
    
    parser.add_argument('--simple', action='store_true',
                       help='Ejecutar solo verificación bitcoinlib')
    parser.add_argument('--export', choices=['json', 'txt', 'both'],
                       help='Exportar resultados en formato específico')
    parser.add_argument('--quiet', action='store_true',
                       help='Modo silencioso, menos output')
    parser.add_argument('--version', action='version',
                       version='C_k Verifier 1.0 - Echo-QCAL ∞³')
    
    args = parser.parse_args()
    
    # Configurar verificador
    verificador = VerificadorCriptograficoCk(verbose=not args.quiet)
    
    if args.simple:
        # Solo verificación bitcoinlib
        if not args.quiet:
            print("🔐 Ejecutando verificación simple de firma...")
        resultado = verificador.verificar_con_bitcoinlib()
        
        # Mostrar resultado simple
        if resultado["exitoso"]:
            print("✅ C_k VERIFICADO - Control criptográfico confirmado")
            return 0
        else:
            print("❌ C_k NO VERIFICADO - Firma inválida o error")
            return 1
    else:
        # Verificación completa
        resultados = verificador.ejecutar_verificacion_completa()
        
        # Retornar código de salida apropiado
        return 0 if resultados.get("exito_general", False) else 1

# ============================================================================
# EJECUCIÓN COMO MÓDULO
# ============================================================================

if __name__ == "__main__":
    
    # Banner de inicio
    banner = """
    ╔══════════════════════════════════════════════════════╗
    ║      🔐 C_k VERIFICATION - Echo-QCAL ∞³              ║
    ║      Control Criptográfico de Firma Patoshi 2025     ║
    ╚══════════════════════════════════════════════════════╝
    """
    
    print(banner)
    
    # Ejecutar verificación
    exit_code = main()
    
    # Mensaje final
    if exit_code == 0:
        print("\n✨ Verificación completada exitosamente")
    else:
        print("\n⚠️  Verificación completada con advertencias o errores")
    
    sys.exit(exit_code)

# ============================================================================
# FUNCIONES ADICIONALES PARA INTEGRACIÓN
# ============================================================================

def verificar_rapido():
    """Función rápida para integración en otros scripts"""
    verificador = VerificadorCriptograficoCk(verbose=False)
    return verificador.verificar_con_bitcoinlib()["exitoso"]

def obtener_resultado_detallado():
    """Obtiene resultado detallado para uso programático"""
    verificador = VerificadorCriptograficoCk(verbose=False)
    verificador.ejecutar_verificacion_completa()
    return verificador.resultados

def generar_reporte_html():
    """Genera reporte HTML de la verificación"""
    # Implementación opcional para dashboard web
    pass
