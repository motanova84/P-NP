import sys
import httpx

def main():
    url = "http://localhost:8000/solve"

    # Instancia 3-SAT de prueba
    payload = {
        "n": 3,
        "clauses": [
            [1, 2, 3],
            [-1, -2, 3]
        ]
    }

    print("📡 Iniciando prueba de coherencia E2E en NOESIS API...")
    try:
        response = httpx.post(url, json=payload, timeout=15.0)
        response.raise_for_status()
    except Exception as e:
        print(f"❌ Error al conectar con la API: {e}")
        sys.exit(1)
        
    data = response.json()
    print(f"✅ Respuesta del sistema: {data}")
    
    # Criterios de aceptación E2E
    assert data["is_sat"] is True, "Instancia declarada UNSAT cuando debía ser SAT."
    assert data["psi"] >= 0.333333, f"Coherencia bajo la barrera: {data['psi']}"
    assert len(data["assignment"]) == 3, "Asignación devuelta incompleta."
    
    print("🌊 Validación E2E exitosa. Coherencia confirmada.")


if __name__ == "__main__":
    main()
