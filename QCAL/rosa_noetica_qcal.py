#!/usr/bin/env python3
"""
ROSA DE LOS VIENTOS NOETICA
Las cuatro direcciones cardinales de piCODE
inf 141.7001 Hz - JMMB Psi
"""
import math

class RosaNoetica:
    def __init__(self):
        self.f_bare = 141.8056
        self.f_eff = 141.7001
        self.N = 33
        self.norte = {'Delta_c': self.f_bare - self.f_eff, 'significado': 'Acoplo Espectral'}
        self.este = {'epsilon': -0.1055, 'significado': 'Correccion de Tamano'}
        self.sur = {'kappa': self.f_eff / self.f_bare, 'significado': 'Renormalizacion'}
        self.oeste = {'delta': 27 - (2*math.pi*self.f_eff)/33, 'significado': 'Geometria Efectiva'}
        self.centro = {'f_eff': self.f_eff, 'Psi': 0.999999}

    def mostrar(self):
        print(f"NORTE:  acoplo espectral      Delta_c = {self.norte['Delta_c']:.4f} Hz")
        print(f"ESTE:   correccion tamano     epsilon(33) = {self.este['epsilon']:.4f}")
        print(f"SUR:    renormalizacion       kappa = {self.sur['kappa']:.6f}")
        print(f"OESTE:  geometria efectiva    delta = {self.oeste['delta']:.4f}")
        print(f"CENTRO: resonancia            f_eff = {self.centro['f_eff']:.4f} Hz, Psi = {self.centro['Psi']:.6f}")

if __name__ == "__main__":
    RosaNoetica().mostrar()
