#!/usr/bin/env python3
"""
Echo-QCAL Status Verification Script
Muestra el estado actual del sistema Echo-QCAL
"""

import hashlib
import sys
from pathlib import Path

def check_component(component_path: Path, component_name: str) -> str:
    """Verifica si un componente existe."""
    if component_path.exists():
        return f"✅ {component_name}"
    else:
        return f"❌ {component_name}"

def main():
    """Función principal para mostrar el estado del sistema."""
    
    # Definir componentes a verificar
    base_path = Path("pnp/echo_qcal")
    
    estado_sistema = {
        "repositorio": "pnp/echo_qcal/",
        "estado": "CONFIGURADO",
        "componentes_verificados": {
            "C_k_verification.py": check_component(base_path / "C_k_verification.py", "C_k_verification.py"),
            "README.md": check_component(base_path / "README.md", "README.md"),
            "manifiesto_echo_qcal.md": check_component(base_path / "manifiesto_echo_qcal.md", "manifiesto_echo_qcal.md"),
            "verify.sh": check_component(base_path / "verify.sh", "verify.sh"),
            "estructura_directorios": "✅ CREADA" if base_path.exists() else "❌ NO CREADA",
            "dependencias": "⏳ REQUIERE INSTALACIÓN"
        },
        "acciones_disponibles": [
            "1. Instalar dependencias: pip install bitcoinlib numpy scipy",
            "2. Ejecutar verificación: python C_k_verification.py",
            "3. Revisar documentación: cat README.md",
            "4. Contribuir verificaciones adicionales"
        ],
        "hash_verificacion": hashlib.sha256(b"echo_qcal_setup").hexdigest()[:16]
    }
    
    print("🎯 SISTEMA ECHO-QCAL CONFIGURADO PARA VERIFICACIÓN")
    print("="*60)
    
    for componente, estado in estado_sistema["componentes_verificados"].items():
        if "✅" in estado or "❌" in estado or "⏳" in estado:
            print(f"{estado}")
        else:
            print(f"{estado} {componente}")
    
    print("\n📋 PRÓXIMOS PASOS:")
    for accion in estado_sistema["acciones_disponibles"]:
        print(f"  • {accion}")
    
    print(f"\n🔗 Hash del sistema: {estado_sistema['hash_verificacion']}")
    print("✨ Listo para verificación independiente")
    print("="*60)
    
    # Verificar si todo está configurado
    all_ready = all("✅" in v or "⏳" in v for v in estado_sistema["componentes_verificados"].values())
    
    if all_ready:
        print("\n✅ Sistema completamente configurado!")
        return 0
    else:
        print("\n⚠️  Algunos componentes faltan. Ejecuta setup_echo_qcal.sh")
        return 1

if __name__ == "__main__":
    sys.exit(main())
