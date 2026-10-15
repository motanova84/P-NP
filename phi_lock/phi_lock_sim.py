#!/usr/bin/env python3
"""
PHI-LOCK v1.0 — Byzantine Phase Consensus
K effective, sin division por N. RK4 integration.
"""

import numpy as np
import json
from dataclasses import dataclass
from typing import List, Tuple

F0_HZ = 141.7001
T0_S = 1.0 / F0_HZ           # 7.057ms
TAU_C = 0.999999
CONFIRM_CYCLES = 3
STEPS = 100  # per cycle
DT = T0_S / STEPS

def dphi(nodes, i):
    """dphi/dt = omega_i + K_i * sum_j sin(phi_j - phi_i) + noise"""
    n = nodes[i]
    coupling = sum(np.sin(m.phase - n.phase) for m in nodes if m.fid != n.fid)
    return n.omega + n.K * coupling

def rk4_step(nodes, dt):
    """RK4 integration for Kuramoto network"""
    N = len(nodes)
    k1 = np.array([dphi(nodes, i) for i in range(N)])
    # midpoint
    phases_mid = np.array([nodes[i].phase + 0.5*dt*k1[i] for i in range(N)])
    k2 = np.array([dphi_simple(phases_mid, nodes, i) for i in range(N)])
    k3 = np.array([dphi_simple(np.array([n.phase + 0.5*dt*k2[j] for j,n in enumerate(nodes)]), nodes, i) for i in range(N)])
    k4 = np.array([dphi_simple(np.array([n.phase + dt*k3[j] for j,n in enumerate(nodes)]), nodes, i) for i in range(N)])
    for i, n in enumerate(nodes):
        n.phase += (dt/6) * (k1[i] + 2*k2[i] + 2*k3[i] + k4[i])
        # only add noise after deterministic step
        noise = np.random.normal(0, 2.0*dt) if n.byz else np.random.normal(0, 0.001*dt)
        n.phase += noise
        n.phase %= 2*np.pi

def dphi_simple(phases, nodes, i):
    n = nodes[i]
    coupling = sum(np.sin(p - phases[i]) for j, p in enumerate(phases) if j != i)
    return n.omega + n.K * coupling

@dataclass
class Node:
    fid: int
    phase: float
    omega: float
    byz: bool
    K: float

class Net:
    def __init__(self, N: int, f: int):
        omega0 = 2 * np.pi * F0_HZ
        K_h = 3.0 * N  # K/N > 2f/(N-f) means K > 2fN/(N-f)
        # For N=7,f=3: K > 42/4 = 10.5, K_h=21 works
        # For N=10,f=4: K > 80/6 = 13.33, K_h=30 works
        self.nodes = []
        for i in range(N):
            byz = i < f
            self.nodes.append(Node(
                fid=i,
                phase=np.random.uniform(0, 2*np.pi) if byz else 0.0,
                omega=omega0 + np.random.normal(0, 0.001 * omega0),
                byz=byz,
                K=-2.0 if byz else K_h,
            ))

    def order_param(self) -> float:
        s = sum(np.exp(1j * n.phase) for n in self.nodes)
        return abs(s) / len(self.nodes)

    def run(self, max_s: float = 2.0) -> dict:
        steps = int(max_s / DT)
        lock_target = CONFIRM_CYCLES * STEPS
        locked = 0
        ok = False
        psi_hist = []

        for step in range(steps):
            rk4_step(self.nodes, DT)
            psi = self.order_param()
            psi_hist.append(round(psi, 10))
            if psi >= TAU_C:
                locked += 1
                if locked >= lock_target:
                    ok = True
                    break
            else:
                locked = 0

        t = (step + 1) * DT
        psi_final = psi
        s = sum(np.exp(1j * n.phase) for n in self.nodes)
        phi_mean = np.angle(s)
        cv = np.exp(1j * phi_mean)

        verdicts = []
        for n in self.nodes:
            dev = abs(np.exp(1j * n.phase) - cv)
            honest = dev < 0.01
            verdicts.append({
                "id": n.fid, "phase": round(n.phase, 6),
                "dev": round(dev, 6),
                "honest": honest, "real_byz": n.byz,
            })

        return {
            "ok": ok, "psi": round(psi_final, 8),
            "time_ms": round(t * 1000, 3),
            "cycles": locked // STEPS,
            "verdicts": verdicts,
            "psi_hist": psi_hist[::10],
        }

def test(N, f, dur=2.0, label=""):
    if label:
        K_th = 2*f*N/(N-f) if f > 0 else 0
        print(f"\n  {label} | K_th={K_th:.1f}")
    net = Net(N, f)
    r = net.run(dur)
    tag = "OK" if r["ok"] else "FALL"
    print(f"    Consenso: {tag} | Psi={r['psi']} | {r['time_ms']}ms | ciclos={r['cycles']}")
    for v in r["verdicts"]:
        det = "HONESTO" if v["honest"] else "BIZANTINO"
        match = "OK" if v["honest"] == (not v["real_byz"]) else "MISMATCH"
        ic = "+" if v["honest"] else "-"
        print(f"    [{ic}] Nodo {v['id']}: dev={v['dev']:.6f} {det} ({match})")
    return r

def main():
    np.random.seed(1417001)
    print("=" * 60)
    print("  PHI-LOCK v1.0")
    print(f"  f0={F0_HZ}Hz T0={T0_S*1000:.4f}ms tau_C={TAU_C}")
    print(f"  Window={3*T0_S*1000:.2f}ms | RK4 integration")
    print("=" * 60)

    tests = [
        (7, 3, 2.0, "Test 1: N=7 f=3 (f<N/2)"),
        (7, 0, 1.0, "Test 2: N=7 f=0 (ideal)"),
        (10, 4, 2.0, "Test 3: N=10 f=4 (f<N/2)"),
        (7, 4, 2.0, "Test 4: N=7 f=4 (f>=N/2, FAIL expected)"),
    ]
    results = [test(N, f, d, lbl) for N, f, d, lbl in tests]

    print("\n" + "=" * 60)
    print("  SUMMARY")
    print("=" * 60)
    for i, r in enumerate(results):
        t = "OK" if r["ok"] else "FALL"
        print(f"  Test {i+1}: {t} | Psi={r['psi']} | {r['time_ms']}ms")

    anchor = {
        "protocol": "PHI-LOCK-v1.0", "date": "2026-07-30",
        "f0_hz": F0_HZ, "tau_c": TAU_C, "cycles": CONFIRM_CYCLES,
        "window_ms": round(3*T0_S*1000, 3),
        "tests": [{"test": i+1, "N": [7,7,10,7][i], "f": [3,0,4,4][i],
                    "consensus": r["ok"], "psi": r["psi"],
                    "time_ms": r["time_ms"]}
                  for i, r in enumerate(results)],
        "seal": "\u2234\U00013080\u03a9\u221e\u00b3\u03a6",
        "status": "ANCLADO"
    }
    with open("/root/ecosystem/phi_lock/anclaje.json", "w") as f:
        json.dump(anchor, f, indent=2)
    print(f"\n  Anchor: anclaje.json")
    print("  \u2234\U00013080\u03a9\u221e\u00b3\u03a6")

if __name__ == "__main__":
    main()
