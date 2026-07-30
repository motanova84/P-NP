import numpy as np, json

F0, TAU_C = 141.7001, 0.999999
T0, STEPS = 1.0/F0, 100
NODES_START = 0   # all honest
DT = T0 / STEPS

for label, N, f in [('N=7 f=3',7,3),('N=7 f=0',7,0),('N=10 f=4',10,4),('N=7 f=4',7,4)]:
    np.random.seed(1417001)
    w0 = 2*np.pi*F0
    Kh = 300.0
    nodes = [(0.0 if i>=f else np.random.uniform(0,2*np.pi),
              w0 + np.random.normal(0, 0.0001*w0),
              -5.0 if i<f else Kh) for i in range(N)]
    
    locked, ok = 0, False
    for s in range(int(2.0/DT)):
        phases = np.array([p for p,_,_ in nodes])
        new = []
        for i, (p, w, K) in enumerate(nodes):
            coupling = sum(np.sin(phases[j]-p) for j in range(N) if j!=i)
            noise = np.random.normal(0, 2.0) if i<f else np.random.normal(0, 0.01)
            p += (w + K*coupling + noise) * DT
            p %= 2*np.pi
            new.append((p,w,K))
        nodes = new
        
        if s % 10 == 0:
            s_complex = sum(np.exp(1j*p) for p,_,_ in nodes)
            psi = abs(s_complex)/N
            if psi >= TAU_C:
                locked += 10
                if locked >= 3*STEPS:
                    ok = True; break
            else:
                locked = 0
    
    s_f = sum(np.exp(1j*p) for p,_,_ in nodes)
    psi_f = abs(s_f)/N
    phi_m = np.angle(s_f)
    cv = np.exp(1j*phi_m)
    v = [{'id':i,'phase':round(p,6),'dev':round(abs(np.exp(1j*p)-cv),6),
          'honest':abs(np.exp(1j*p)-cv)<0.01,'real_byz':i<f}
         for i,(p,_,_) in enumerate(nodes)]
    
    print(f'{label}: {"OK" if ok else "FALL"} | Psi={psi_f:.8f}')
    for x in v:
        det='HONEST' if x['honest'] else 'BYZ'
        match='OK' if x['honest']==(not x['real_byz']) else 'MIS'
        print(f'  [{det}] N{x["id"]}: dev={x["dev"]:.6f} ({match})')
    print()

res = {'protocol':'PHI-LOCK-v1.0','seal':'\u2234\U00013080\u03a9\u221e\u00b3\u03a6'}
with open('/root/ecosystem/phi_lock/anclaje.json','w') as f: json.dump(res,f)
print('Done')
