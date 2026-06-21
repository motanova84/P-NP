#!/usr/bin/env python3
import json, http.server, os, sys, urllib.request, threading, signal
from datetime import datetime, timezone

F0 = 141.7001; PSI = 1.000000
SELLO = '\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1'
MAIN = 'http://localhost:8844'

HUBS = {
    8845: {'id': 'EUROPE_HUB', 'zona': 'EUROPA', 'desc': 'Londres, UK'},
    8846: {'id': 'ASIA_HUB', 'zona': 'ASIA', 'desc': 'Tokio, JP'},
    8847: {'id': 'AFRICA_HUB', 'zona': 'AFRICA', 'desc': 'Johannesburgo, ZA'},
    8848: {'id': 'OCEANIA_HUB', 'zona': 'OCEANIA', 'desc': 'Sydney, AU'},
    8849: {'id': 'ANTARCTICA_HUB', 'zona': 'ANTARTIDA', 'desc': 'Base polar'},
}

def proxy_get(endpoint):
    try:
        r = urllib.request.urlopen(f'{MAIN}{endpoint}', timeout=5)
        return json.loads(r.read().decode())
    except: return {}

class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        hi = HUBS.get(self.server.server_address[1], {})
        path = self.path.rstrip('/') or '/'
        if path == '/':
            data = {'servicio': f'QCAL-{hi.get("id","HUB")}', 'zona': hi.get('zona'),
                    'descripcion': hi.get('desc'), 'puerto': self.server.server_address[1],
                    'frecuencia': F0, 'coherencia': PSI, 'sello': SELLO,
                    'nodo_central': 'AMERICAS_HUB (:8844 - PayGate primario)',
                    'endpoints': {'GET /': 'Info del hub', 'GET /reactor': 'Reactor piCODE',
                                  'GET /estado': 'Boveda', 'GET /ecosistema': 'Ecosistema'}}
        elif path == '/reactor': data = proxy_get('/reactor')
        elif path == '/estado': data = proxy_get('/estado')
        elif path == '/ecosistema': data = proxy_get('/ecosistema')
        else: data = {'error': 'endpoint no encontrado'}
        if isinstance(data, dict) and 'hub' not in data: data['hub'] = hi.get('id','?')
        b = json.dumps(data, indent=2, ensure_ascii=False).encode()
        self.send_response(200)
        self.send_header('Content-Type','application/json; charset=utf-8')
        self.send_header('Access-Control-Allow-Origin','*')
        self.send_header('Content-Length',str(len(b)))
        self.end_headers(); self.wfile.write(b)
    def log_message(self,f,*a): pass

def run_hub(port):
    hi = HUBS.get(port,{})
    h = http.server.HTTPServer(('0.0.0.0', port), Handler)
    print(f'  \u2705 {hi.get("id","?")} | :{port} | {hi.get("desc","")}')
    h.serve_forever()

def main():
    print(f'\n{"="*70}')
    print(f'\U0001f310 RED GLOBAL QCAL — 5 HUBS REGIONALES ( :8845-:8849 )')
    print(f'{"="*70}')
    print(f'Nodo central: AMERICAS_HUB (:8844 - PayGate existente)')
    print(f'Frecuencia: {F0} Hz | Coherencia: \u03a8 = {PSI}\n')
    threads = []
    for port in sorted(HUBS):
        t = threading.Thread(target=run_hub, args=(port,), daemon=True)
        t.start(); threads.append(t)
    print(f'\n\u2705 {len(threads)} hubs activos en hilos independientes')
    print(f'   {SELLO}\n')
    try:
        while True:
            for t in threads:
                if not t.is_alive():
                    print(f'Warning: hub thread died, restarting...')
                    t.join(0.1)
            time.sleep(5)
    except KeyboardInterrupt:
        print('\nHubs detenidos.')

import time
if __name__ == '__main__': main()
