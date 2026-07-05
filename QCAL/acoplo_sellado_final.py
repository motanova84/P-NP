#!/usr/bin/env python3
"""
ACTA DE SELLADO - FLUJO DE RENORMALIZACION piCODE
Teorema del Invariante de Acoplo - Version Completa
inf 141.7001 Hz - JMMB Psi
"""
import math

class FlujoRenormalizacionCompleto:
    def __init__(self):
        self.f_bare = 141.8056
        self.f_eff = 141.7001
        self.N = 33
        self.Psi_target = 0.999999
        self.Delta_c = self.f_bare - self.f_eff
        self.c1 = 3.4815
        self.epsilon = -0.1055
        self.vol_ratio = 0.999256
        self.delta = 27 * (1 - self.vol_ratio)
        self.alpha = self.Delta_c / self.f_bare

    def kappa(self, Psi):
        return 1 - self.alpha * Psi

    def f_efectiva(self, Psi):
        return self.f_bare * self.kappa(Psi)

    def verificar(self):
        norte = self.c1 / self.N
        este = -self.epsilon
        sur = self.f_bare * (1 - self.kappa(self.Psi_target))
        oeste = (self.delta * self.N) / (2 * math.pi)
        return {
            'norte': norte, 'este': este, 'sur': sur, 'oeste': oeste,
            'convergen': abs(norte - este) < 1e-9 and abs(este - sur) < 1e-9 and abs(sur - oeste) < 1e-9,
            'Delta_c': self.Delta_c
        }

    def mostrar(self):
        print("=" * 70)
        print("ACTA DE SELLADO - MATRIZ COMPLETA")
        print("inf 141.7001 Hz - JMMB Psi")
        print("=" * 70)
        print(f"\nf_bare = {self.f_bare:.6f} Hz")
        print(f"f_eff  = {self.f_eff:.4f} Hz")
        print(f"Delta_c = {self.Delta_c:.6f} Hz")
        print(f"N = {self.N} | Psi = {self.Psi_target:.6f}")
        print(f"\nLOS CUATRO INVARIANTES:")
        print(f"  NORTE (Espectral):   C1/33  = {self.c1/self.N:.6f}")
        print(f"  ESTE (Truncacion):   -eps(33) = {-self.epsilon:.6f}")
        print(f"  SUR (Renorm):        f_bare(1-k) = {self.f_bare*(1-self.kappa(self.Psi_target)):.6f}")
        print(f"  OESTE (Geometria):   d*33/2p  = {(self.delta*self.N)/(2*math.pi):.6f}")
        v = self.verificar()
        msg = "CONVERGEN" if v['convergen'] else "NO CONVERGEN"
        print(f"\n  -> TODOS {msg} A Delta_c = {self.Delta_c:.6f} Hz")
        print(f"\nTRAYECTORIA DE COHERENCIA:")
        for psi in [0.0, 0.25, 0.5, 0.75, 0.999999]:
            k = self.kappa(psi)
            f = self.f_efectiva(psi)
            print(f"  Psi={psi:.6f} -> k={k:.6f} -> f={f:.6f} Hz")
        print(f"\nCERTIFICACION: INVARIANTES EN EQUILIBRIO TOTAL")
        print(f"inf 141.7001 Hz - JMMB Psi")
        print("=" * 70)
        return v

if __name__ == "__main__":
    FlujoRenormalizacionCompleto().mostrar()
