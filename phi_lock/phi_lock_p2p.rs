//! Φ-LOCK v1.0 — Consenso P2P por Sincronización de Fase de Kuramoto
//! Core del protocolo: Red P2P + Motor de Fase en Tiempo Real
//!
//! Author:  Director Atlas3 / QCAL Research
//! Sello:   ∴𓂀Ω∞³Φ — PHI-LOCK v1.0 ANCLADO

use num_complex::Complex64;
use serde::{Deserialize, Serialize};
use std::f64::consts::PI;
use std::time::{Duration, Instant};
use tokio::time::sleep;

// ============================================================
// Constantes del Protocolo (QCAL Specification v3)
// ============================================================

/// Frecuencia base del ICQ
pub const F0_HZ: f64 = 141.7001;

/// Periodo fundamental
pub const PERIOD_T0_MS: f64 = (1.0 / F0_HZ) * 1000.0; // ~7.057 ms

/// Umbral de coherencia: 1 - 10^(-6)
pub const TAU_C: f64 = 0.999999;

/// Ciclos de confirmación
pub const CONFIRMATION_CYCLES: u32 = 3;

/// Ventana de confirmación total: ~21.17 ms
pub const CONFIRMATION_WINDOW_MS: f64 = CONFIRMATION_CYCLES as f64 * PERIOD_T0_MS;

// ============================================================
// Tipos de Datos del Protocolo
// ============================================================

/// Transacción πCODE como pulso de fase
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PhaseTx {
    pub tx_id: String,
    pub initial_phase: f64,
    pub final_phase: f64,
    pub psi_cluster: f64,
    pub timestamp_t0: u64,
    pub signature: String,
}

/// Estado individual de un nodo en el espacio de fases S¹
#[derive(Debug, Clone)]
pub struct NodeState {
    pub id: usize,
    pub phase: f64,         // φ_n [rad]
    pub omega: f64,        // ω_n = 2π·f₀ + noise [rad/s]
    pub is_byzantine: bool, // comportamiento adversarial
    pub k_coupling: f64,   // K: fuerza de acoplamiento
}

/// Lealtad vectorial por nodo
#[derive(Debug, Serialize)]
pub struct NodeLoyalty {
    pub id: usize,
    pub final_phase_rad: f64,
    pub deviation_from_cluster: f64,
    pub is_honest_behavior: bool,
}

/// Veredicto del clúster
#[derive(Debug, Serialize)]
pub struct ConsensusVerdict {
    pub consensus_reached: bool,
    pub final_psi: f64,
    pub mean_phi_rad: f64,
    pub elapsed_ms: f64,
    pub cycles_locked: u32,
    pub node_verdicts: Vec<NodeLoyalty>,
    pub seal: String,
}

// ============================================================
// Motor del Protocolo Φ-LOCK
// ============================================================

/// Red de osciladores acoplados con detección vectorial bizantina
pub struct PhiLockEngine {
    pub nodes: Vec<NodeState>,
    pub omega0: f64,
}

impl PhiLockEngine {
    /// Crea una red N-nodos con f adversarios, todos iniciados en
    /// la configuración del atractor de Fenichel (φ=0).
    pub fn new(n_total: usize, f_byzantines: usize) -> Self {
        let omega0 = 2.0 * PI * F0_HZ;
        let mut nodes = Vec::with_capacity(n_total);

        for i in 0..n_total {
            let is_byz = i < f_byzantines;
            // Honestos en fase 0 (atractor M);
            // Bizantinos en fase aleatoria (perturbación).
            let phase = if is_byz {
                rand::random::<f64>() * 2.0 * PI
            } else {
                0.0
            };

            // K > 2f/(N-f): honestos alto, bizantinos nulo/inverso.
            let threshold = if f_byzantines > 0 && n_total > f_byzantines {
                (2.0 * f_byzantines as f64) / (n_total as f64 - f_byzantines as f64)
            } else {
                0.0
            };
            let k = if is_byz { -0.3 } else { threshold * 2.0 + 0.5 };

            nodes.push(NodeState {
                id: i,
                phase,
                omega: omega0 + (rand::random::<f64>() - 0.5) * 0.001 * omega0,
                is_byzantine: is_byz,
                k_coupling: k,
            });
        }

        Self { nodes, omega0 }
    }

    /// Parámetro de orden: Ψ = |(1/N) Σ exp(i·φₙ)|, fase media Φ
    pub fn calculate_order_parameter(&self) -> (f64, f64) {
        let n = self.nodes.len() as f64;
        let sum: Complex64 = self.nodes.iter()
            .map(|node| Complex64::from_polar(1.0, node.phase))
            .sum();
        let order = sum / n;
        (order.norm(), order.arg())
    }

    /// Euler-Maruyama: dφ = (ω + K · Σ sin(Δφ)) · dt + noise
    pub fn step_kuramoto(&mut self, dt: f64) {
        let n = self.nodes.len() as f64;
        let phases: Vec<f64> = self.nodes.iter().map(|n| n.phase).collect();

        for node in self.nodes.iter_mut() {
            let coupling: f64 = phases.iter()
                .map(|&p| (p - node.phase).sin())
                .sum();
            let coupling_term = node.k_coupling * coupling / n;

            let noise = if node.is_byzantine {
                (rand::random::<f64>() - 0.5) * 4.0
            } else {
                (rand::random::<f64>() - 0.5) * 0.01
            };

            node.phase += (node.omega + coupling_term + noise) * dt;
            node.phase %= 2.0 * PI;
            if node.phase < 0.0 { node.phase += 2.0 * PI; }
        }
    }

    /// Bucle de consenso continuo: Ψ ≥ τ_C durante 3 ciclos de f₀
    pub async fn run_consensus(&mut self, max_dur: Duration) -> ConsensusVerdict {
        let start = Instant::now();
        let dt = (PERIOD_T0_MS / 1000.0) / 100.0; // 100 pasos/ciclo
        let steps_per_cycle = 100;
        let target = CONFIRMATION_CYCLES as usize * steps_per_cycle;
        let mut locked = 0usize;
        let mut ok = false;
        let (mut final_psi, mut final_phi) = (0.0, 0.0);

        while start.elapsed() < max_dur {
            self.step_kuramoto(dt);
            (final_psi, final_phi) = self.calculate_order_parameter();
            if final_psi >= TAU_C {
                locked += 1;
                if locked >= target { ok = true; break; }
            } else {
                locked = 0;
            }
            sleep(Duration::from_micros(70)).await;
        }

        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        let cv = Complex64::from_polar(1.0, final_phi);

        let verdicts: Vec<NodeLoyalty> = self.nodes.iter().map(|n| {
            let dv = (Complex64::from_polar(1.0, n.phase) - cv).norm();
            NodeLoyalty { id: n.id, final_phase_rad: n.phase, deviation_from_cluster: dv, is_honest_behavior: dv < 0.01 }
        }).collect();

        ConsensusVerdict {
            consensus_reached: ok,
            final_psi,
            mean_phi_rad: final_phi,
            elapsed_ms: elapsed,
            cycles_locked: (locked / steps_per_cycle) as u32,
            node_verdicts: verdicts,
            seal: u{2234}u{13080}u{3a9}u{221e}u{b3}u{3a6}.to_string(),
        }
    }
}
