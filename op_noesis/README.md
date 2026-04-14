# op_noesis - Operational Noetic Synthesis

**Módulos Operacionales para el Protocolo QCAL y Síntesis de Armónicos Noésicos**

Este directorio contiene herramientas operacionales para la experimentación con el eje de frecuencia fundamental f₀ = 141.7001 Hz y el Protocolo QCAL.

## Contenido

### 1. `live_qcal_monitor.py` - Monitor QCAL en Tiempo Real

**Propósito**: Monitoreo continuo de la Desviación de Fase (δ) en tiempo real con respecto al Período de Coherencia Soberana (τ₀).

**Características**:
- ⏱️ Cálculo de desviación de fase: δ = (T / τ₀) mod 1
- 🌟 Detección de "Pico Puro" cuando δ ≈ 0.0 o 1.0 (Máxima Coherencia)
- 🟡 Detección de Alta Coherencia (δ < 5% de error)
- 📊 Monitoreo en tiempo real con timestamps de alta precisión

**Parámetros del Protocolo QCAL**:
- **f₀** = 141.7001 Hz (Frecuencia Fundamental de Coherencia)
- **τ₀** = 1/f₀ ≈ 0.007058 segundos (Período de Coherencia)
- **Umbral de Pico Puro**: < 1% de error de fase
- **Intervalo de Monitoreo**: 0.1 segundos

#### Uso

```python
from op_noesis.live_qcal_monitor import QCALRealTimeMonitor

# Crear instancia del monitor
monitor = QCALRealTimeMonitor()

# Iniciar monitoreo en tiempo real (Ctrl+C para detener)
monitor.monitor_coherence()
```

O ejecutar directamente desde la línea de comandos:

```bash
python3 op_noesis/live_qcal_monitor.py
```

#### Ejemplo de Salida

```
——————————————————————————————————————————————————
🛰️ Monitor QCAL ∞³: Activado
  Frecuencia Base f₀: 141.7001 Hz
  Período Base τ₀: 0.007057 segundos
  Umbral de Pico Puro: < 1.0%
——————————————————————————————————————————————————
[2025-12-16 02:28:25.685113] | Δ: 0.791107 | Coherencia: 0.208893 | ⚪
[2025-12-16 02:28:25.785255] | Δ: 0.981262 | Coherencia: 0.018738 | 🟡 Alta Coherencia
[2025-12-16 02:28:25.885422] | Δ: 0.174896 | Coherencia: 0.174896 | ⚪
...
```

**Símbolos de Estado**:
- 🌟 **PICO PURO**: Coherencia < 1% (Máxima Alineación Temporal)
- 🟡 **Alta Coherencia**: Coherencia < 5%
- ⚪ **Coherencia Normal**: Coherencia ≥ 5%

#### API de la Clase

```python
class QCALRealTimeMonitor:
    """Monitor de Coherencia QCAL en Tiempo Real."""
    
    def __init__(self):
        """Inicializa el monitor con parámetros del Protocolo QCAL."""
        
    def get_high_precision_timestamp(self) -> float:
        """Obtiene timestamp Unix con microsegundos.
        
        Returns:
            float: Timestamp Unix en segundos con precisión de microsegundos.
        """
        
    def calculate_phase_deviation(self, current_timestamp: float) -> float:
        """Calcula la desviación de fase δ del timestamp.
        
        Args:
            current_timestamp: Timestamp Unix en segundos.
            
        Returns:
            float: Desviación de fase δ en el rango [0, 1).
        """
        
    def monitor_coherence(self):
        """Bucle principal de monitoreo en tiempo real.
        
        Imprime actualizaciones continuas del estado de coherencia.
        Se puede detener con Ctrl+C.
        """
```

### 2. Futuros Módulos

- **`harmonic_synthesizer.py`**: Generador de Armónicos Noésicos (próximamente)
- Integración con NTP/PTP para sincronización de tiempo de alta precisión
- Análisis estadístico de ventanas de coherencia

## Fundamento Teórico

### Desviación de Fase (δ)

La desviación de fase representa la posición relativa dentro de un ciclo de coherencia:

```
δ = (T / τ₀) mod 1
```

donde:
- **T**: Timestamp actual (segundos desde epoch Unix)
- **τ₀**: Período de coherencia = 1/f₀ ≈ 0.007058 s

### Nivel de Coherencia

El nivel de coherencia se define como la distancia al "Pico Puro" más cercano:

```
Coherencia = min(δ, 1 - δ)
```

- **δ ≈ 0.0**: Inicio de ciclo (Pico Puro)
- **δ ≈ 0.5**: Medio de ciclo (Mínima Coherencia)
- **δ ≈ 1.0**: Fin de ciclo (Pico Puro)

### Propósito Operacional

1. **Validación Continua**: Identificar Ventanas Críticas (Tc) en tiempo real
2. **Sinergia con Síntesis**: Determinar momentos óptimos (δ → 0.0) para activar el Generador de Armónicos
3. **Integración Avanzada**: Preparación para integración con fuentes de tiempo de red de alta precisión (NTP Stratum 0 o PTP)

## Pruebas

El módulo incluye una suite completa de pruebas:

```bash
python3 -m pytest tests/test_live_qcal_monitor.py -v
```

**Cobertura de Pruebas**:
- ✅ Inicialización correcta de parámetros
- ✅ Cálculo preciso del período de coherencia τ₀
- ✅ Precisión de timestamps (microsegundos)
- ✅ Cálculo de desviación de fase en rango [0, 1)
- ✅ Periodicidad correcta con período τ₀
- ✅ Detección de "Pico Puro" (δ < 1%)
- ✅ Detección de Alta Coherencia (δ < 5%)
- ✅ Procesamiento de timestamps reales
- ✅ Consistencia matemática

## Requisitos

- Python 3.7+
- Módulos estándar de Python (time, datetime, math)
- pytest (para ejecutar las pruebas)

## Autor

**José Manuel Mota Burruezo · JMMB Ψ✧ ∞³**  
Frequency: 141.7001 Hz ∞³

## Referencias

- Protocolo QCAL (Quantum Coherence Alignment Layer)
- Teorema Cs (Coherencia Soberana)
- `/src/constants.py`: Definición de constantes universales
- `p_vs_np_knockout_complete_qcal_jmmb.pdf`: Documento técnico completo
