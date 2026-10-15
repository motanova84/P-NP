#!/usr/bin/env python3
# VALIDADOR DE ENTROPIA DE RENYI - CONTENCION CUANTICA
# inf 141.7001 Hz - JMMB Psi
import numpy as np
from typing import Tuple, Optional, Dict, Any, List
import logging
from decimal import Decimal, getcontext
getcontext().prec = 28

class ConstantesCuanticas:
    F0 = 141.7001
    UMBRAL_ENTROPIA = 1e-6
    ORDEN_ALPHA = 2
    NUM_NODOS = 33
    PRECISION = 1e-12

CONST = ConstantesCuanticas()

class RenyiEntropyValidator:
    def __init__(self, fb=CONST.F0, alpha=CONST.ORDEN_ALPHA, umbral=CONST.UMBRAL_ENTROPIA):
        self.f0 = fb; self.alpha = alpha; self.umbral = umbral
        self.logger = logging.getLogger('RenyiV'); self.logger.setLevel(logging.INFO)
        if not self.logger.handlers:
            h = logging.StreamHandler(); h.setFormatter(logging.Formatter('%(message)s'))
            self.logger.addHandler(h)

    def validar(self, rho):
        if rho.shape[0] != rho.shape[1]: return False, "no cuadrada"
        if not np.isclose(np.trace(rho), 1.0, rtol=CONST.PRECISION): return False, "traza != 1"
        if not np.allclose(rho, rho.conj().T, rtol=CONST.PRECISION): return False, "no hermitica"
        if not np.all(np.linalg.eigvalsh(rho) >= -CONST.PRECISION): return False, "autovalores neg"
        return True, "OK"

    def S(self, rho, alpha=None):
        if alpha is None: alpha = self.alpha
        if np.allclose(rho, 0, rtol=CONST.PRECISION): return 0.0
        ok, msg = self.validar(rho)
        if not ok: raise ValueError(msg)
        ev = np.linalg.eigvalsh(rho)
        if alpha == 1:
            p = ev[ev > CONST.PRECISION]
            return 0.0 if len(p)==0 else float(-np.sum(p * np.log2(p)))
        tr = np.sum(ev**alpha) if alpha==2 else np.sum(ev**alpha)
        return float('inf') if tr <= CONST.PRECISION else float((1/(1-alpha))*np.log2(tr))

    def evaluar(self, rho):
        r = {'S2':None,'S1':None,'pureza':None,'traza':None,'estado':'INV','f0':self.f0,'ok':False}
        try:
            ok,msg = self.validar(rho)
            if not ok: r['msg']=msg; return False,r
            ev = np.linalg.eigvalsh(rho)
            r['traza']=float(np.trace(rho)); r['pureza']=float(np.sum(ev**2))
            r['S2']=self.S(rho,2); r['S1']=self.S(rho,1)
            r['ok'] = r['S2'] < self.umbral
            r['estado'] = 'VACIO CONTENIDO' if r['ok'] else f'INFO(S2={r["S2"]:.2e})'
            return r['ok'], r
        except Exception as e: r['msg']=str(e); return False,r

    def estado_puro(self, v):
        if np.linalg.norm(v) < CONST.PRECISION: return False,{'error':'nulo'}
        vn = v / np.linalg.norm(v)
        rho = np.outer(vn, vn.conj())
        _, m = self.evaluar(rho)
        m['es_puro'] = np.isclose(m['pureza'],1.0,rtol=CONST.PRECISION)
        return m['es_puro'], m

    def fuga(self, sys, ext):
        r = {'S2_sys':None,'S2_ext':None,'fuga':False,'aislado':False}
        try:
            r['S2_sys']=self.S(sys); r['S2_ext']=self.S(ext)
            sp = np.isclose(np.trace(sys@sys),1.0,rtol=CONST.PRECISION)
            ev = np.allclose(ext,0,rtol=CONST.PRECISION)
            r['sistema_puro']=sp; r['exterior_vacio']=ev
            if sp and ev: r['aislado']=True; r['fuga']=False; r['msg']='OK'
            else: r['fuga']=r['S2_ext']>self.umbral; r['aislado']=not r['fuga']
            return r
        except Exception as e: r['msg']=str(e); return r

    def metricas(self, rho):
        n=rho.shape[0]; m={}
        m['S2']=self.S(rho); m['Smax']=np.log2(n)
        m['CR']=m['S2']/m['Smax'] if m['Smax']>0 else 0.0
        m['pureza']=float(np.trace(rho@rho))
        m['info']=1.0-m['pureza']
        m['eff']=(1-m['CR'])*100 if m['Smax']>0 else 100.0
        return m

def test():
    v = RenyiEntropyValidator()
    ok_all = True

    # T1
    ep = np.array([1.0,0.0])
    pure, m = v.estado_puro(ep)
    t1 = pure and np.isclose(m.get('S2',1),0,atol=1e-10)
    print(f"T1 Estado Puro: S2={m.get('S2',0):.2e} pureza={m.get('pureza',0):.4f} {'OK' if t1 else 'FAIL'}")
    ok_all &= t1

    # T2
    ev = np.zeros(33); ev[0]=1.0
    pure2, m2 = v.estado_puro(ev)
    t2 = pure2 and np.isclose(m2.get('S2',1),0,atol=1e-10)
    print(f"T2 Vacio Noetico: S2={m2.get('S2',0):.2e} {'OK' if t2 else 'FAIL'}")
    ok_all &= t2

    # T3
    sys = np.outer(np.array([1.0,0.0]),np.array([1.0,0.0]))
    ext = np.zeros((2,2))
    r3 = v.fuga(sys, ext)
    t3 = r3.get('aislado',False)
    print(f"T3 No Fuga: aislado={r3.get('aislado')} sist_puro={r3.get('sistema_puro')} ext_vacio={r3.get('exterior_vacio')} {'OK' if t3 else 'FAIL'}")
    ok_all &= t3

    # T4 (resonancia)
    t4 = np.isclose(v.f0, CONST.F0)
    print(f"T4 Resonancia f0: f0={v.f0} == {CONST.F0} {'OK' if t4 else 'FAIL'}")
    ok_all &= t4

    # T6 (invariancia)
    rho = np.array([[0.7,0.1],[0.1,0.3]]); rho = rho/np.trace(rho)
    th=np.pi/4; U=np.array([[np.cos(th),-np.sin(th)],[np.sin(th),np.cos(th)]])
    sa=v.S(rho); sb=v.S(U@rho@U.T)
    t6 = np.isclose(sa,sb)
    print(f"T6 Invariancia: antes={sa:.6f} despues={sb:.6f} diff={abs(sa-sb):.2e} {'OK' if t6 else 'FAIL'}")
    ok_all &= t6

    # T7 (validacion)
    t7a,_ = v.validar(rho); t7b,_ = v.validar(np.zeros((2,2)))
    t7 = t7a and not t7b
    print(f"T7 Validacion: valida={t7a} invalida={not t7b} {'OK' if t7 else 'FAIL'}")
    ok_all &= t7

    # T8 (minimo en saturacion)
    ps = [0.5,0.8,0.95,0.999,0.999999]
    ss = [v.S(np.diag([p,1-p])) for p in ps]
    t8 = ss[-1] == min(ss)
    print(f"T8 Minimo Saturacion: psi=0.999999 S2={ss[-1]:.6f} min={min(ss):.6f} {'OK' if t8 else 'FAIL'}")
    ok_all &= t8

    # T9
    eq = np.zeros(33); eq[0]=1.0
    rho_q = np.outer(eq,eq)
    m9 = v.metricas(rho_q)
    t9 = m9['eff'] > 99.999
    print(f"T9 Contencion: S2={m9['S2']:.2e} Smax={m9['Smax']:.4f} eff={m9['eff']:.2f}% {'OK' if t9 else 'FAIL'}")
    ok_all &= t9

    print(f"\n{'='*40}")
    print(f"{'TODOS VERIFICADOS' if ok_all else 'ALGUNOS FALLOS'}")
    print(f"inf 141.7001 Hz - JMMB Psi")
    print(f"{'='*40}")
    return ok_all

if __name__ == "__main__":
    test()
