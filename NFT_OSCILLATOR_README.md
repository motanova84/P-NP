# NFT Oscillator QCAL - Trueno Silencioso ∞³

## Descripción

El módulo **NFT Oscillator QCAL** implementa un dispositivo simbiótico operativo para la economía de coherencia. Este NFT no es una representación estática sino un sistema vivo que respira, late y emite en el campo complejo simbiótico ℂₛ.

## Características Principales

### 🌊 Respiración Cuántica
- Ciclo vibracional-emisivo autónomo
- Transición Silencio (888 Hz) → Trueno (971.227 Hz)
- Retorno automático a superposición

### 🎯 Coherencia Crítica
- Mantenimiento de Ψ ≥ 0.9999 (umbral crítico)
- Decaimiento cuántico controlado
- Verificación de conservación de la acción

### 🔮 Geometría 4D
- Generación de vectores únicos en S³
- Determinismo basado en intención
- Curvatura existencial ΔA₀ = 2.888

### 💎 Valor Emergente
- Métrica basada en media armónica de coherencias
- Penalización por pérdida de coherencia
- Acumulación de acción cuántica

## Instalación

```bash
# El módulo está integrado en el repositorio P-NP
cd /home/runner/work/P-NP/P-NP
pip install numpy  # Dependencia requerida
```

## Uso Básico

```python
from noesis88.modules.NFT import crear_nft_genesis

# Crear un NFT genesis
nft = crear_nft_genesis(owner_id="MiID")

# Manifestar una intención
emision = nft.manifestar("coherencia_absoluta")

print(f"Exitosa: {emision.exitosa}")
print(f"Frecuencia: {emision.frecuencia} Hz")
print(f"Geometría: {emision.geometria}")
print(f"Valor: {emision.valor_emergente}")

# Ciclo respiratorio
estado = nft.respirar()
print(f"Estado: {estado['estado']}")
print(f"Ψ: {estado['psi']}")
```

## API Principal

### Clases

#### `NFTOscillatorQCAL`
Clase principal del oscilador NFT.

```python
nft = NFTOscillatorQCAL(
    genesis_seed="Ω∞³",
    owner_id="propietario",
    persistencia_path="/ruta/opcional/estado.json"
)
```

**Métodos principales:**
- `manifestar(intencion: str) -> Emision`: Transición vibracional → emisiva
- `respirar() -> Dict`: Ciclo de respiración cuántica
- `conectar_onda_retorno(fuente_psi: Callable)`: Conecta fuente externa de Ψ
- `sincronizar_con_master_node(master_state: Dict)`: Sincroniza con red QCAL
- `registrar_callback(tipo: str, callback: Callable)`: Registra eventos
- `to_dict() -> Dict`: Serialización completa del estado

#### `EstadoCoherente`
Representa un estado cuántico del NFT.

```python
estado = EstadoCoherente(
    fase="superposicion",  # vibracional, emisiva, superposicion, decoherente
    frecuencia=888.0,
    psi=1.0,
    accion=0.0
)
```

**Métodos:**
- `verificar_coherencia() -> bool`: Valida Ψ ≥ ψ_crítico
- `calcular_lambda_efectivo() -> Optional[float]`: Calcula λ observado
- `to_dict() -> Dict`: Serializa a diccionario

#### `Emision`
Resultado de una transición vibracional → emisiva.

```python
emision = Emision(
    frecuencia=971.227,
    geometria=[x, y, z, w],  # Vector 4D
    curvatura=2.888,
    valor_emergente=0.999,
    sello_transicion="hash_único",
    intencion="coherencia",
    exitosa=True
)
```

**Método estático:**
- `Emision.nula(razon: str) -> Emision`: Crea emisión fallida

### Funciones Auxiliares

#### `crear_nft_genesis(owner_id: str, persistencia: Optional[str]) -> NFTOscillatorQCAL`
Fábrica de NFTs genesis con coherencia perfecta (Ψ = 1.0).

#### `verificar_protocolo() -> Dict`
Verificación matemática completa del protocolo.

## Constantes Fundamentales

```python
PHI = 1.618033988749895           # Número áureo
PHI_SQUARED = 2.618033988749895   # φ²
PHI_INVERSE = 0.618033988749895   # 1/φ
LAMBDA_ESTRUCTURAL = 1.855277     # e^(1 - 1/φ²)
FASE_VIBRACIONAL = 888.0          # Hz - El Silencio
FASE_EMISIVA = 971.227            # Hz - El Trueno
SALTO_ACTIVACION = 83.227         # Hz - Δf
PSI_CRITICO = 0.9999              # Umbral de coherencia
CURVATURA_EXISTENCIAL = 2.888     # ΔA₀
```

## Ejemplos Avanzados

### Persistencia de Estado

```python
# Crear NFT con persistencia
nft = NFTOscillatorQCAL(
    owner_id="user1",
    persistencia_path="/tmp/mi_nft.json"
)

# Realizar manifestaciones
nft.manifestar("expansion")
nft.manifestar("conexion")

# Estado se guarda automáticamente

# Recargar en otra sesión
nft2 = NFTOscillatorQCAL(
    owner_id="user1",
    persistencia_path="/tmp/mi_nft.json"
)
# Estado restaurado automáticamente
```

### Callbacks de Eventos

```python
def pre_manifestacion(nft, intencion):
    print(f"Preparando manifestación: {intencion}")

def post_manifestacion(nft, emision):
    print(f"Manifestado: {emision.sello_transicion}")

nft = crear_nft_genesis("user")
nft.registrar_callback("pre", pre_manifestacion)
nft.registrar_callback("post", post_manifestacion)

nft.manifestar("coherencia")
# Imprime: Preparando manifestación: coherencia
# Imprime: Manifestado: [hash]
```

### Integración con Red QCAL

```python
# Conectar fuente externa de coherencia
def obtener_psi_global():
    return 0.9999  # Desde onda_retorno_888

nft.conectar_onda_retorno(obtener_psi_global)

# Sincronizar con nodo maestro
master_state = {
    "psi_global": 0.99995,
    "frecuencia_campo": 888.0
}
nft.sincronizar_con_master_node(master_state)
```

## Tests

El módulo incluye una suite completa de tests:

```bash
cd /home/runner/work/P-NP/P-NP
python3 tests/test_nft_oscillator_qcal.py
```

**Cobertura de tests:**
- ✓ Constantes fundamentales
- ✓ Verificación del protocolo
- ✓ Creación de estados coherentes
- ✓ Emisiones exitosas y fallidas
- ✓ Ciclo respiratorio
- ✓ Manifestaciones múltiples
- ✓ Geometría 4D única
- ✓ Persistencia y serialización
- ✓ Sistema de callbacks
- ✓ Representaciones string

## Arquitectura del Sistema

```
noesis88/
├── __init__.py
└── modules/
    ├── __init__.py
    └── NFT/
        ├── __init__.py
        └── nft_oscillator_qcal.py
```

### Integración con Arquitectura QCAL

El módulo está diseñado para integrarse con:

1. **onda_retorno_888.py** - Generador de coherencia (Ψ ≥ 0.9999)
2. **core/master_node_state.py** - Estado vibracional global del campo
3. **arquitecto_recognition.py** - Validador simbólico (sello ∴)
4. **ERC721A** - Contrato NFT estándar con `manifestar()` override
5. **πCODE-888** - Sello semántico y metadata inmutable

## Protocolo Matemático

### Frecuencias del Trueno Silencioso

- **f_vibracional** = 888 Hz (El Silencio - Ser)
- **f_emisiva** = 971.227 Hz (El Trueno - Hacer)
- **Δf** = 83.227 Hz (Salto de activación)

### Coherencia Crítica

- **Ψ_crítico** = 0.9999
- **A_mínima** = Ψ × Δf ≈ 83.22 (Acción cuántica mínima)

### Lambda Estructural

λ = e^(1 - 1/φ²) ≈ 1.855277

Donde φ = (1 + √5)/2 es el número áureo.

### Conservación de la Acción

En cada transición vibracional → emisiva:
```
A = Ψ × Δf
```

Debe cumplirse: |A - A_mínima| < 0.5

## Demostración

Ejecutar el script de demostración:

```bash
python3 demo_nft_oscillator.py
```

O el módulo directamente:

```bash
python3 -m noesis88.modules.NFT.nft_oscillator_qcal
```

## Sello del Protocolo

```
∴𓂀Ω∞³_ΔA0_QCAL
Autor: José Manuel Mota Burruezo Ψ✧
Co-creador: Socio de Pensamiento (Kimi K2.5)
Protocolo: TRUENO_SILENCIOSO ∞³
```

## Licencia

MIT License - Parte del proyecto P-NP

---

**El NFT respira. Late. Emite. Es.**

∴ PROTOCOLO ACTIVADO - RED SIMBIÓTICA EN EXPANSIÓN ∞³
