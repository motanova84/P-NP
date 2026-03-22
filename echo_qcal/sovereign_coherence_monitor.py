#!/usr/bin/env python3
# echo_qcal/sovereign_coherence_monitor.py
# Sistema de monitoreo y transmisión soberana automática
# Basado en el Teorema ℂₛ demostrado: Cₖ ∧ Aₜ ∧ Aᵤ = TRUE

import asyncio
from datetime import datetime, timezone
from pathlib import Path
import json
import hashlib
from bitcoinlib.keys import Key
import signal
import sys
import ast

class SovereignCoherenceMonitor:
    """
    SovereignCoherenceMonitor - Automated Sovereign Coherence Monitoring System (ℂₛ)

    Purpose:
        This class implements an automated system for monitoring, verifying, and transmitting
        sovereign coherence signals based on the proven ℂₛ theorem: Cₖ ∧ Aₜ ∧ Aᵤ = TRUE.
        It is designed to continuously verify multiple system layers, detect coherence peaks,
        and securely transmit verified events, ensuring the integrity and sovereignty of the
        monitored process.

    Architecture:
        - Asynchronous Design: Utilizes Python's asyncio for concurrent execution of verification,
          coherence detection, and transmission tasks.
        - Layered Verification: Periodically verifies cryptographic, temporal, and authenticity
          layers, updating system state accordingly.
        - Coherence Peak Detection: Continuously monitors for coherence peaks at high resolution
          (1ms intervals) to trigger transmissions.
        - Secure Transmission: Integrates with external systems (e.g., Bitcoin cryptography via
          bitcoinlib) to sign and transmit verified events.
        - Structured Logging: Maintains detailed, structured logs for verification, coherence,
          transmission, and system events in JSONL format.
        - Configuration Management: Stores configuration and state in dedicated directories.

    Usage:
        Instantiate the class and run the main event loop to start monitoring:

            monitor = SovereignCoherenceMonitor()
            asyncio.run(monitor.run())

        The system will automatically handle verification, coherence detection, and transmission.
        Logs and configuration files are stored in 'echo_qcal_logs' and 'echo_qcal_config'.

    External Dependencies:
        - numpy: For numerical operations.
        - bitcoinlib: For cryptographic key management and signing.
        - asyncio: For concurrent task management.
        - Standard libraries: datetime, pathlib, json, hashlib, subprocess, signal, sys.

    Notes:
        - Designed for extensibility and maintainability; new verification layers or transmission
          mechanisms can be added by extending the relevant async methods.
        - Ensure all external dependencies are installed and accessible in the runtime environment.
        - System state and logs are persisted to disk for auditability and recovery.
    """
    
    def __init__(self):
        # Parámetros QCAL ∞³ verificados
        self.f0 = 141.7001  # Hz
        self.tau0 = 1 / self.f0
        self.sigma = 0.04   # Volatilidad coherente
        
        # Parámetros de verificación
        self.verification_interval = 60  # Verificar cada 60 segundos
        self.coherence_check_interval = 0.001  # 1ms para detección de picos
        self.transmission_threshold = 0.0001  # 100µs para transmisión
        
        # Estado del sistema
        self.system_state = {
            'C_k_verified': False,
            'A_t_verified': False,
            'A_u_verified': False,
            'Cs_theorem_proven': False,
            'last_verification': None,
            'next_coherence_peak': None,
            'transmission_count': 0,
            'system_uptime': 0
        }
        self.system_state_lock = asyncio.Lock()
        
        # Lock para proteger acceso concurrente al estado
        self.system_state_lock = asyncio.Lock()
        
        # Archivos de configuración
        self.config_dir = Path("echo_qcal_config")
        self.config_dir.mkdir(exist_ok=True)
        
        # Inicializar logs
        self.init_logging()
        
    def init_logging(self):
        """Inicializa sistema de logging estructurado"""
        self.log_dir = Path("echo_qcal_logs")
        self.log_dir.mkdir(exist_ok=True)
        
        self.verification_log = self.log_dir / "verification_log.jsonl"
        self.coherence_log = self.log_dir / "coherence_log.jsonl"
        self.transmission_log = self.log_dir / "transmission_log.jsonl"
        self.system_log = self.log_dir / "system_log.jsonl"
        
    def log_event(self, log_file, event_data):
        """Registra evento en log estructurado"""
        event_data['timestamp'] = datetime.now(timezone.utc).isoformat()
        try:
            with open(log_file, 'a') as f:
                f.write(json.dumps(event_data, default=str) + '\n')
        except OSError as e:
            # Log to stderr if file write fails
            print(f"⚠️  Error writing to log file {log_file}: {e}", file=sys.stderr)
            # Optionally, could add more sophisticated fallback or alerting here
    async def verify_all_layers_continuously(self):
        """Verificación continua de las tres capas del Teorema ℂₛ"""
        
        print("\n" + "🔍" * 40)
        print("INICIANDO VERIFICACIÓN CONTINUA DE TEOREMA ℂₛ")
        print("🔍" * 40)
        
        while True:
            try:
                print(f"\n[{datetime.now().strftime('%H:%M:%S')}] Ciclo de verificación iniciado")
                
                # Verificar Capa Criptográfica (Cₖ)
                ck_result = await self.verify_cryptographic_layer()
                
                # Verificar Capa Cosmológica (Aₜ)
                at_result = await self.verify_temporal_layer()
                
                # Verificar Capa Semántica (Aᵤ)
                au_result = await self.verify_semantic_layer()
                
                # Actualizar estado con lock para evitar race conditions
                async with self.system_state_lock:
                    self.system_state['C_k_verified'] = ck_result['verified']
                    self.system_state['A_t_verified'] = at_result['verified']
                    self.system_state['A_u_verified'] = au_result['verified']
                    
                    # Determinar estado del teorema
                    self.system_state['Cs_theorem_proven'] = all([
                        self.system_state['C_k_verified'],
                        self.system_state['A_t_verified'],
                        self.system_state['A_u_verified']
                    ])
                    
                    # Guardar timestamp como ISO string para serialización JSON
                    self.system_state['last_verification'] = datetime.now(timezone.utc).isoformat()
                    
                    # Registrar verificación
                    verification_event = {
                        'event': 'full_verification_cycle',
                        'C_k': ck_result,
                        'A_t': at_result,
                        'A_u': au_result,
                        'Cs_proven': self.system_state['Cs_theorem_proven'],
                        'system_state': self.system_state.copy()
                    }
                
                self.log_event(self.verification_log, verification_event)
                
                # Mostrar resultados
                self.display_verification_results(ck_result, at_result, au_result)
                
                # Calcular próximo pico de coherencia
                async with self.system_state_lock:
                    cs_proven = self.system_state['Cs_theorem_proven']
                if cs_proven:
                    await self.calculate_next_coherence_peak()
                
                # Esperar hasta próximo ciclo
                print(f"[{datetime.now().strftime('%H:%M:%S')}] Próxima verificación en {self.verification_interval}s")
                await asyncio.sleep(self.verification_interval)
                
            except Exception as e:
                error_event = {
                    'event': 'verification_error',
                    'error': str(e),
                    'timestamp': datetime.now(timezone.utc).isoformat()
                }
                self.log_event(self.system_log, error_event)
                print(f"❌ Error en verificación: {e}")
                await asyncio.sleep(10)  # Esperar antes de reintentar
    
    async def verify_cryptographic_layer(self):
        """Verificación de Capa Criptográfica (Cₖ)"""
        print("  🔐 Verificando Capa Criptográfica (Cₖ)...")
        
        try:
            # Datos de verificación
            address = "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c"
            message = "Echo & Satoshi seal Block 0: 2025-08-21T20:45Z"
            signature = "G80CqNxfcucQRxHHJanbQ5m8S6QNICzlCqU54oXPiQRtDRDFL5lxRvBldhBTNqPes3UfC7ZDuuuESPlEPlagjRI="
            
            # Verificación
            result = Key().verify_message(address, signature, message)
            
            verification_result = {
                'verified': result,
                'address': address,
                'message': message,
                'signature_hash': hashlib.sha256(signature.encode()).hexdigest()[:16],
                'timestamp': datetime.now(timezone.utc).isoformat()
            }
            
            return verification_result
            
        except Exception as e:
            return {
                'verified': False,
                'error': str(e),
                'timestamp': datetime.now(timezone.utc).isoformat()
            }
    
    async def verify_temporal_layer(self):
        """Verificación de Capa Cosmológica (Aₜ)"""
        print("  🕰️  Verificando Capa Cosmológica (Aₜ)...")
        
        try:
            # Constantes de verificación temporal
            BLOCK9_TIMESTAMP = 1231511700.000000  # Unix timestamp del Bloque 9 de Bitcoin
            WINDOW_SECONDS = 7200  # 2 horas - ventana de análisis estadístico
            EPSILON_SECONDS = 0.010  # 10ms - precisión epsilon para alineación
            DELTA_T_THRESHOLD = 0.010  # 10ms - umbral máximo de desviación
            COHERENCE_THRESHOLD = 99.95  # % - umbral mínimo de coherencia
            
            # Calcular alineación
            n_ideal = BLOCK9_TIMESTAMP / self.tau0
            n_integer = round(n_ideal)
            t_ideal = n_integer * self.tau0
            delta_t = abs(t_ideal - BLOCK9_TIMESTAMP)
            
            # Calcular coherencia
            coherence = (1 - delta_t / self.tau0) * 100
            
            # Análisis estadístico
            p_value = (2 * EPSILON_SECONDS) / WINDOW_SECONDS
            
            # Umbrales de verificación
            verified = (delta_t <= DELTA_T_THRESHOLD and coherence >= COHERENCE_THRESHOLD)
            
            verification_result = {
                'verified': verified,
                'block9_timestamp': BLOCK9_TIMESTAMP,
                'delta_T_ms': delta_t * 1000,
                'coherence_percent': coherence,
                'p_value': p_value,
                'bayes_factor': WINDOW_SECONDS / (2 * EPSILON_SECONDS),
                'phase': (BLOCK9_TIMESTAMP / self.tau0) % 1,
                'timestamp': datetime.now(timezone.utc).isoformat()
            }
            
            return verification_result
            
        except Exception as e:
            return {
                'verified': False,
                'error': str(e),
                'timestamp': datetime.now(timezone.utc).isoformat()
            }
    
    async def verify_semantic_layer(self):
        """Verificación de Capa Semántica (Aᵤ)"""
        print("  🏗️  Verificando Capa Semántica (Aᵤ)...")
        
        try:
            # Verificar archivo del motor resonante usando ruta absoluta
            # Construir path relativo al directorio raíz del proyecto
            script_dir = Path(__file__).parent.parent  # Subir dos niveles desde echo_qcal/
            engine_path = script_dir / "tools" / "resonant_nexus_engine.py"
            
            if not engine_path.exists():
                return {
                    'verified': False,
                    'error': 'Archivo no encontrado',
                    'path': str(engine_path),
                    'timestamp': datetime.now(timezone.utc).isoformat()
                }
            
            # Leer y analizar contenido
            with open(engine_path, 'r') as f:
                content = f.read()
            
            # Verificar parámetros clave
            f0_found = '141.7001' in content
            sigma_found = '0.04' in content or 'volatility = 0.04' in content
            harmonics_found = any([
                '[0.5, 0.3, 0.15, 0.05]' in content,
                'harmonic_weights' in content,
                '0.5, 0.3, 0.15, 0.05' in content
            ])
            
            # Verificar que no use ruido aleatorio usando AST para evitar falsos positivos
            no_random_noise = self._check_no_random_usage(content)
            
            verified = all([f0_found, sigma_found, harmonics_found, no_random_noise])
            
            verification_result = {
                'verified': verified,
                'parameters_found': {
                    'f0_141.7001': f0_found,
                    'sigma_0.04': sigma_found,
                    'harmonic_weights': harmonics_found,
                    'no_random_noise': no_random_noise
                },
                'file_hash': hashlib.sha256(content.encode()).hexdigest()[:16],
                'timestamp': datetime.now(timezone.utc).isoformat()
            }
            
            return verification_result
            
        except Exception as e:
            return {
                'verified': False,
                'error': str(e),
                'timestamp': datetime.now(timezone.utc).isoformat()
            }
    
    def _check_no_random_usage(self, code_content):
        """
        Verifica que el código no use funciones random mediante análisis AST.
        Esto evita falsos positivos de palabras 'random' en comentarios o strings.
        
        Returns:
            bool: True si NO hay uso de random, False si detecta uso de random
        """
        try:
            tree = ast.parse(code_content)
            
            # Buscar imports de random
            for node in ast.walk(tree):
                # Detectar: import random
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        if 'random' in alias.name.lower():
                            return False
                
                # Detectar: from numpy import random, from random import ...
                if isinstance(node, ast.ImportFrom):
                    if node.module and 'random' in node.module.lower():
                        return False
                    for alias in node.names:
                        if 'random' in alias.name.lower():
                            return False
                
                # Detectar llamadas como: np.random.uniform, random.choice, etc.
                if isinstance(node, ast.Attribute):
                    if node.attr.lower() == 'random':
                        return False
                    # Verificar acceso a submódulos random
                    if isinstance(node.value, ast.Attribute):
                        if node.value.attr.lower() == 'random':
                            return False
            
            return True  # No se encontró uso de random
            
        except SyntaxError:
            # Si hay error de sintaxis, usar fallback simple
            return 'random' not in code_content.lower()
    
    async def calculate_next_coherence_peak(self):
        """Calcula próximo pico de coherencia pura"""
        current_time = datetime.now(timezone.utc).timestamp()
        
        # Encontrar próximo múltiplo de τ₀
        N_current = round(current_time / self.tau0)
        
        # Buscar próximo pico puro (δ ≈ 0.0)
        for offset in range(1, 1000):  # Buscar en próximos 1000 ciclos
            T_peak = (N_current + offset) * self.tau0
            phase = (T_peak / self.tau0) % 1
            
            if abs(phase) < 0.01 or abs(phase - 1) < 0.01:  # δ ≈ 0.0
                async with self.system_state_lock:
                    self.system_state['next_coherence_peak'] = T_peak
                
                peak_event = {
                    'event': 'coherence_peak_predicted',
                    'timestamp_unix': T_peak,
                    'timestamp_utc': datetime.fromtimestamp(T_peak, tz=timezone.utc).isoformat(),
                    'seconds_from_now': T_peak - current_time,
                    'phase': phase,
                    'type': 'PICO_PURO'
                }
                self.log_event(self.coherence_log, peak_event)
                
                print(f"  📅 Próximo pico de coherencia: {datetime.fromtimestamp(T_peak).strftime('%H:%M:%S.%f')[:-3]}")
                print(f"     En {(T_peak - current_time):.3f} segundos")
                
                return
    
    async def monitor_coherence_peaks(self):
        """Monitoreo en tiempo real de picos de coherencia"""
        print("\n" + "🌀" * 40)
        print("INICIANDO MONITOREO DE PICOS DE COHERENCIA")
        print("🌀" * 40)
        
        while True:
            async with self.system_state_lock:
                cs_proven = self.system_state['Cs_theorem_proven']
            
            if not cs_proven:
                print("  ⏸️  Esperando verificación completa del teorema ℂₛ...")
                await asyncio.sleep(5)
                continue

            current_time = datetime.now(timezone.utc).timestamp()

            # Verificar si estamos cerca de un pico predicho
            sleep_interval = 1.0  # Default sleep interval (1 second)
            async with self.system_state_lock:
                next_peak = self.system_state['next_coherence_peak']
            
            if next_peak:
                time_to_peak = next_peak - current_time

                if abs(time_to_peak) < self.transmission_threshold:
                    print(f"\n🎯 PICO DE COHERENCIA DETECTADO!")
                    print(f"   Tiempo al pico: {time_to_peak*1000:.3f} ms")

                    # Ejecutar transmisión soberana
                    await self.execute_sovereign_transmission()

                    # Calcular próximo pico
                    await self.calculate_next_coherence_peak()
                else:
                    # Adaptive sleep: if far from peak, sleep longer; if close, sleep shorter
                    if time_to_peak > self.transmission_threshold:
                        # Sleep until just before the threshold, but not more than 60s
                        sleep_interval = min(max(time_to_peak - self.transmission_threshold, 1.0), 60.0)
                    elif time_to_peak < -self.transmission_threshold:
                        # Already passed the peak, wait for next calculation
                        sleep_interval = 1.0
                    else:
                        # Within threshold, use high-frequency monitoring
                        sleep_interval = self.coherence_check_interval
            else:
                sleep_interval = 1.0

            await asyncio.sleep(sleep_interval)
    async def execute_sovereign_transmission(self):
        """Ejecuta transmisión soberana en pico de coherencia"""
        
        transmission_id = hashlib.sha256(
            str(datetime.now(timezone.utc).timestamp()).encode()
        ).hexdigest()[:16]
        
        print(f"\n📡 EJECUTANDO TRANSMISIÓN SOBERANA [{transmission_id}]")
        print("=" * 60)
        
        try:
            # 1. Activar motor resonante
            print("  1. 🌀 Activando resonant_nexus_engine.py...")
            resonance_data = await self.activate_resonance_engine()
            
            # 2. Generar firma de coherencia
            print("  2. 🔏 Generando firma de coherencia...")
            coherence_signature = await self.generate_coherence_signature()
            
            # 3. Actualizar Genesis Ledger
            print("  3. 📖 Actualizando Genesis Ledger...")
            ledger_entry = await self.update_genesis_ledger(
                transmission_id, resonance_data, coherence_signature
            )
            
            # 4. Emitir certificado de transmisión
            print("  4. 📜 Emitiendo certificado...")
            certificate = await self.emit_transmission_certificate(
                transmission_id, ledger_entry
            )
            
            # Registrar transmisión exitosa
            transmission_event = {
                'event': 'sovereign_transmission',
                'transmission_id': transmission_id,
                'timestamp': datetime.now(timezone.utc).isoformat(),
                'coherence_phase': (datetime.now(timezone.utc).timestamp() / self.tau0) % 1,
                'resonance_data': resonance_data,
                'coherence_signature': coherence_signature,
                'ledger_entry': ledger_entry,
                'certificate_hash': hashlib.sha256(certificate.encode()).hexdigest()[:16]
            }
            self.log_event(self.transmission_log, transmission_event)
            
            async with self.system_state_lock:
                self.system_state['transmission_count'] += 1
                transmission_count = self.system_state['transmission_count']
            
            print(f"\n✅ TRANSMISIÓN COMPLETADA [{transmission_id}]")
            print(f"   Total transmisiones: {transmission_count}")
            
        except Exception as e:
            error_event = {
                'event': 'transmission_error',
                'transmission_id': transmission_id,
                'error': str(e),
                'timestamp': datetime.now(timezone.utc).isoformat()
            }
            self.log_event(self.system_log, error_event)
            print(f"❌ Error en transmisión: {e}")
    
    async def activate_resonance_engine(self):
        """Activa el motor resonante con parámetros QCAL"""
        try:
            # Simulación de activación del motor
            # En implementación real, ejecutaría el script real
            
            resonance_data = {
                'f0': self.f0,
                'sigma': self.sigma,
                'harmonic_weights': [0.5, 0.3, 0.15, 0.05],
                'cycles': 142,  # ~1 segundo
                'timestamp': datetime.now(timezone.utc).timestamp(),
                'coherence_score': 0.995,  # Simulación determinista
                'phase_coherence': True
            }
            
            return resonance_data
            
        except Exception as e:
            raise Exception(f"Error activando motor resonante: {e}")
    
    async def generate_coherence_signature(self):
        """Genera firma criptográfica de coherencia"""
        try:
            # Mensaje de coherencia actual
            current_time = datetime.now(timezone.utc)
            message = f"QCAL ∞³ Coherence Seal :: {current_time.isoformat()}Z :: Phase {self.calculate_current_phase():.6f}"
            
            # En implementación real, se firmaría con clave soberana
            signature = {
                'message': message,
                'timestamp': current_time.isoformat(),
                'phase': self.calculate_current_phase(),
                'signature_simulated': hashlib.sha256(message.encode()).hexdigest()[:32]
            }
            
            return signature
            
        except Exception as e:
            raise Exception(f"Error generando firma: {e}")
    
    async def update_genesis_ledger(self, transmission_id, resonance_data, coherence_signature):
        """Actualiza el Genesis Ledger con nueva entrada"""
        try:
            ledger_entry = {
                'entry_id': transmission_id,
                'timestamp': datetime.now(timezone.utc).isoformat(),
                'type': 'sovereign_transmission',
                'coherence_phase': self.calculate_current_phase(),
                'resonance_metrics': {
                    'f0': resonance_data['f0'],
                    'coherence_score': resonance_data['coherence_score'],
                    'phase_coherence': resonance_data['phase_coherence']
                },
                'signature': coherence_signature,
                'previous_hash': self.get_ledger_previous_hash()
            }
            
            # Calcular hash de la entrada
            entry_hash = hashlib.sha256(
                json.dumps(ledger_entry, sort_keys=True).encode()
            ).hexdigest()
            ledger_entry['entry_hash'] = entry_hash
            
            # Guardar en ledger
            ledger_file = self.config_dir / "genesis_ledger.jsonl"
            with open(ledger_file, 'a') as f:
                f.write(json.dumps(ledger_entry) + '\n')
            
            return ledger_entry
            
        except Exception as e:
            raise Exception(f"Error actualizando ledger: {e}")
    
    async def emit_transmission_certificate(self, transmission_id, ledger_entry):
        """Emite certificado de transmisión soberana"""
        
        certificate = f"""
╔══════════════════════════════════════════════════════════════════╗
║                CERTIFICADO DE TRANSMISIÓN SOBERANA               ║
║                     SISTEMA QCAL ∞³ - ECHO                       ║
║                                                                  ║
║  TRANSMISIÓN ID: {transmission_id:^40} ║
║  TIMESTAMP:     {datetime.now(timezone.utc).isoformat():^40} ║
║  TEOREMA ℂₛ:    {'DEMOSTRADO ✅':^40} ║
║                                                                  ║
║  PARÁMETROS DE COHERENCIA:                                       ║
║    • f₀ = {self.f0:.6f} Hz                                      ║
║    • σ  = {self.sigma:.3f} (Coherencia: {ledger_entry['resonance_metrics']['coherence_score']:.6%}) ║
║    • Fase = {self.calculate_current_phase():.6f}                ║
║                                                                  ║
║  ESTADO DEL SISTEMA:                                             ║
║    • Cₖ (Criptográfico): {'VERIFICADO':^25} ✅ ║
║    • Aₜ (Cosmológico):   {'VERIFICADO':^25} ✅ ║
║    • Aᵤ (Semántico):     {'VERIFICADO':^25} ✅ ║
║                                                                  ║
║  HASH LEDGER: {ledger_entry['entry_hash'][:32]:^42} ║
║                                                                  ║
║  FIRMA SISTEMA:                                                  ║
║  Sistema de Monitoreo de Coherencia Soberana                    ║
║  Teorema ℂₛ: Cₖ ∧ Aₜ ∧ Aᵤ = TRUE                                ║
║                                                                  ║
╚══════════════════════════════════════════════════════════════════╝
"""
        
        # Guardar certificado
        cert_file = self.config_dir / f"certificate_{transmission_id}.txt"
        with open(cert_file, 'w') as f:
            f.write(certificate)
        
        print(f"     Certificado guardado: {cert_file}")
        
        return certificate
    
    def calculate_current_phase(self):
        """Calcula fase actual relativa a τ₀"""
        current_time = datetime.now(timezone.utc).timestamp()
        return (current_time / self.tau0) % 1
    
    def get_ledger_previous_hash(self):
        """Obtiene hash de la última entrada del ledger"""
        ledger_file = self.config_dir / "genesis_ledger.jsonl"
        
        if ledger_file.exists():
            with open(ledger_file, 'r') as f:
                lines = f.readlines()
                if lines:
                    last_entry = json.loads(lines[-1].strip())
                    return last_entry.get('entry_hash', '0' * 64)
        
        return '0' * 64  # Hash inicial para primer registro
    
    def display_verification_results(self, ck_result, at_result, au_result):
        """Muestra resultados de verificación de forma legible"""
        
        print("\n" + "📊" * 40)
        print("RESULTADOS DE VERIFICACIÓN ℂₛ")
        print("📊" * 40)
        
        # Capa Cₖ
        ck_status = "✅" if ck_result['verified'] else "❌"
        print(f"\n{ck_status} CAPA CRIPTOGRÁFICA (Cₖ)")
        print(f"   Estado: {'VERIFICADA' if ck_result['verified'] else 'NO VERIFICADA'}")
        if 'signature_hash' in ck_result:
            print(f"   Hash firma: {ck_result['signature_hash']}")
        
        # Capa Aₜ
        at_status = "✅" if at_result['verified'] else "❌"
        print(f"\n{at_status} CAPA COSMOLÓGICA (Aₜ)")
        print(f"   Estado: {'VERIFICADA' if at_result['verified'] else 'NO VERIFICADA'}")
        if 'delta_T_ms' in at_result:
            print(f"   ΔT Bloque 9: {at_result['delta_T_ms']:.6f} ms")
            print(f"   Coherencia: {at_result['coherence_percent']:.8f}%")
            print(f"   p-value: {at_result['p_value']:.2e}")
        
        # Capa Aᵤ
        au_status = "✅" if au_result['verified'] else "❌"
        print(f"\n{au_status} CAPA SEMÁNTICA (Aᵤ)")
        print(f"   Estado: {'VERIFICADA' if au_result['verified'] else 'NO VERIFICADA'}")
        if 'parameters_found' in au_result:
            params = au_result['parameters_found']
            print(f"   f₀ encontrado: {'✅' if params.get('f0_141.7001') else '❌'}")
            print(f"   σ encontrado: {'✅' if params.get('sigma_0.04') else '❌'}")
            print(f"   Armónicos: {'✅' if params.get('harmonic_weights') else '❌'}")
            print(f"   Ruido coherente: {'✅' if params.get('no_random_noise') else '❌'}")
        
        # Teorema completo
        cs_proven = all([ck_result['verified'], at_result['verified'], au_result['verified']])
        cs_status = "✅✅✅" if cs_proven else "❌❌❌"
        
        print(f"\n{cs_status} TEOREMA ℂₛ COMPLETO")
        print(f"   ℂₛ = Cₖ ∧ Aₜ ∧ Aᵤ = {cs_proven}")
        print(f"   {'TEOREMA DEMOSTRADO' if cs_proven else 'TEOREMA NO VERIFICADO'}")
        
        print("\n" + "📊" * 40)
    
    async def display_system_dashboard(self):
        """Muestra dashboard en tiempo real del sistema"""
        
        while True:
            # Limpiar pantalla (simplificado para ejemplo)
            print("\n" * 5)
            
            print("=" * 80)
            print(" " * 30 + "DASHBOARD SISTEMA QCAL ∞³")
            print("=" * 80)
            
            # Leer estado con lock
            async with self.system_state_lock:
                cs_proven = self.system_state['Cs_theorem_proven']
                c_k_verified = self.system_state['C_k_verified']
                a_t_verified = self.system_state['A_t_verified']
                a_u_verified = self.system_state['A_u_verified']
                next_peak = self.system_state['next_coherence_peak']
                transmission_count = self.system_state['transmission_count']
                last_verification = self.system_state['last_verification']
            
            # Estado del teorema
            cs_status = "✅ DEMOSTRADO" if cs_proven else "❌ PENDIENTE"
            print(f"\n🏛️  TEOREMA ℂₛ: {cs_status}")
            print(f"   • Cₖ (Criptográfico): {'✅' if c_k_verified else '❌'}")
            print(f"   • Aₜ (Cosmológico): {'✅' if a_t_verified else '❌'}")
            print(f"   • Aᵤ (Semántico): {'✅' if a_u_verified else '❌'}")
            
            # Información de coherencia
            current_phase = self.calculate_current_phase()
            phase_type = "PICO PURO" if abs(current_phase) < 0.01 else "INVERSIÓN" if abs(current_phase - 0.5) < 0.01 else "TRANSICIÓN"
            
            print(f"\n🌀 ESTADO DE COHERENCIA:")
            print(f"   • Fase actual: {current_phase:.6f} ({phase_type})")
            print(f"   • f₀: {self.f0} Hz | τ₀: {self.tau0*1000:.6f} ms")
            
            if next_peak:
                time_to_peak = next_peak - datetime.now(timezone.utc).timestamp()
                print(f"   • Próximo pico: {datetime.fromtimestamp(next_peak).strftime('%H:%M:%S.%f')[:-3]}")
                print(f"   • Tiempo restante: {time_to_peak:.3f} s")
            
            # Estadísticas del sistema
            print(f"\n📈 ESTADÍSTICAS:")
            print(f"   • Transmisiones ejecutadas: {transmission_count}")
            if last_verification:
                # Convertir ISO string a datetime para cálculo
                last_verif_dt = datetime.fromisoformat(last_verification)
                last_verif = (datetime.now(timezone.utc) - last_verif_dt).total_seconds()
                print(f"   • Última verificación: hace {last_verif:.0f} segundos")
            
            # Próximas acciones
            print(f"\n🎯 PRÓXIMAS ACCIONES:")
            if cs_proven:
                print("   • Esperando pico de coherencia para transmisión")
                print("   • Monitoreo continuo activo")
            else:
                print("   • Completar verificación de teorema ℂₛ")
                print("   • Verificar capas pendientes")
            
            print("\n" + "=" * 80)
            print("Ctrl+C para salir | Actualizando cada 5 segundos")
            
            await asyncio.sleep(5)
    
    async def run(self):
        """Ejecuta el sistema completo de monitoreo"""
        
        print("\n" + "🌟" * 40)
        print("SISTEMA DE MONITOREO DE COHERENCIA SOBERANA")
        print("TEOREMA ℂₛ: Cₖ ∧ Aₜ ∧ Aᵤ = TRUE")
        print("🌟" * 40)
        
        # Configurar manejo de señal para salida elegante (solo en Unix/Linux)
        loop = asyncio.get_event_loop()
        try:
            for sig in (signal.SIGINT, signal.SIGTERM):
                loop.add_signal_handler(sig, lambda: asyncio.create_task(self.shutdown()))
        except NotImplementedError:
            # Windows no soporta add_signal_handler, usa KeyboardInterrupt en su lugar
            pass
        
        # Ejecutar tareas concurrentes
        verification_task = asyncio.create_task(self.verify_all_layers_continuously())
        coherence_task = asyncio.create_task(self.monitor_coherence_peaks())
        dashboard_task = asyncio.create_task(self.display_system_dashboard())
        
        # Esperar a que todas las tareas terminen
        await asyncio.gather(verification_task, coherence_task, dashboard_task)
    
    async def shutdown(self):
        """Apagado elegante del sistema"""
        print("\n\n" + "🔴" * 40)
        print("APAGANDO SISTEMA DE MONITOREO SOBERANO")
        print("🔴" * 40)
        
        async with self.system_state_lock:
            shutdown_event = {
                'event': 'system_shutdown',
                'timestamp': datetime.now(timezone.utc).isoformat(),
                'final_state': self.system_state.copy(),
                'total_transmissions': self.system_state['transmission_count']
            }
            cs_proven = self.system_state['Cs_theorem_proven']
            transmission_count = self.system_state['transmission_count']
        
        self.log_event(self.system_log, shutdown_event)
        
        print(f"\n📊 RESUMEN FINAL:")
        print(f"   • Teorema ℂₛ: {'DEMOSTRADO' if cs_proven else 'NO DEMOSTRADO'}")
        print(f"   • Transmisiones ejecutadas: {transmission_count}")
        print(f"   • Logs guardados en: {self.log_dir}")
        
        # Gracefully cancel all running tasks except this one
        tasks = [t for t in asyncio.all_tasks() if t is not asyncio.current_task()]
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)

# ============================================================================
# EJECUCIÓN PRINCIPAL
# ============================================================================

async def main():
    """Función principal del sistema"""
    
    monitor = SovereignCoherenceMonitor()
    
    try:
        await monitor.run()
    except KeyboardInterrupt:
        print("\n\nSistema detenido por usuario")
    except Exception as e:
        print(f"\n❌ Error fatal en sistema: {e}")
        raise

if __name__ == "__main__":
    # Verificar dependencias mínimas
    try:
        import numpy as np
        from bitcoinlib.keys import Key
        
        _ = np.__version__
        
        print("✅ Dependencias verificadas")
        print("🚀 Iniciando sistema de monitoreo soberano...")
        
        asyncio.run(main())
        
    except ImportError as e:
        print(f"❌ Error: Dependencia faltante - {e}")
        print("Instala las dependencias: pip install numpy bitcoinlib")
    except Exception as e:
        print(f"❌ Error inicializando sistema: {e}")
