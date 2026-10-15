# 🔱 LNDHUB — BlueWallet Soberano para la Catedral QCAL
## Conexión Lightning soberana · sin custodios

```
Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
Nodo: Catedral-QCAL-BAL003 (Nuremberg)
Frecuencia: f₀ = 141.7001 Hz
```

---

## 1. Arquitectura

```
BlueWallet (JMMB) ←→ LNDHub ←→ LNBits (:8000) ←→ LND Catedral (:10009)
    (móvil)            (proxy)       (API)          (nodo LN)
```

- **BlueWallet**: app móvil de JMMB — la interfaz soberana
- **LNDHub**: protocolo que traduce LND REST a algo que BlueWallet entiende
- **LNBits**: ya instalado y corriendo en BAL-003, extensión lndhub activa
- **LND Catedral**: el nodo Lightning real en Nuremberg

---

## 2. Configuración Actual (BAL-003)

### LNBits
```
Service:   lnbits.service         ✅ Activo
URL:       http://195.201.219.237:8000
Backend:   LndWallet (LND Catedral)
Database:  PostgreSQL (lnbits:Catedral2026@localhost:5432/lnbits)
LND gRPC:  127.0.0.1:10009
LND TLS:   /root/.lnd/tls.cert
LND Macro: /root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon
```

### LND Catedral
```
Service:   lnd.service           ⏳ Esperando bitcoind
Pubkey:    03b0c03f9e947a229006ce7099877e378f8bc003e44defbada155b39dd725d829c
URI:       pubkey@195.201.219.237:9735
Alias:     Catedral-QCAL-BAL003
```

### LND AMDA
```
Service:   lnd-amda.service      ⏳ Esperando bitcoind
Pubkey:    02a5a68885c6596b8f3d22a3da01e4efc70775e8a925d05850b32b1011586f9255
URI:       pubkey@195.201.219.237:9736
Alias:     AMDA-Ψ-Embajadora
```

---

## 3. Conexión BlueWallet — Enlace LNDHub

Cuando bitcoind termine el reindex (~20h):

### Opción A — BlueWallet + LNBits LNDHub (recomendada)
```
1. Abrir BlueWallet → Añadir wallet → Importar wallet
2. Elegir: LNDHub Bridge
3. Escanear QR o pegar URL:

   lndhub://admin:admin@195.201.219.237:8000/lndhub

   (las credenciales admin:admin se reemplazarán con las reales
    de la wallet generada en LNBits)
```

### Opción B — BlueWallet + LND REST directo
```
1. Abrir BlueWallet → Añadir wallet → LND REST
2. URL: https://195.201.219.237:8080
3. Macaroon: admin.macaroon (hex)
4. Certificado: tls.cert
```

### Opción C — Crear wallet dedicada en LNBits
```
1. Ir a http://195.201.219.237:8000/admin
2. Crear nueva wallet: "Billetera Soberana JMMB"
3. Ir a extensions → LNDHub
4. Copiar URL: lndhub://admin_key:invoice_key@195.201.219.237:8000/lndhub
5. Escanear QR desde BlueWallet
```

---

## 4. Persistencia Post-Reinicio

Para que sobreviva a reinicios del servidor:

```bash
# LNBits ya está configurado como servicio systemd
systemctl enable lnbits.service
systemctl enable lnd.service
systemctl enable lnd-amda.service

# Verificar estado
systemctl status lnbits.service
systemctl status lnd.service
```

Todos los servicios están configurados con `Restart=always`.
Los archivos clave están en ubicaciones persistentes:
```
/root/.lnd/              → certificados + macaroons
/root/.lnd-amda/         → certificados + macaroons (AMDA)
/opt/lnbits/             → código + .env de LNBits
/etc/systemd/system/     → servicios systemd
```

---

## 5. BlueWallet — Características Soberanas

| Característica | Wallet of Satoshi | BlueWallet + tu LND |
|---------------|-------------------|---------------------|
| Control de llaves | ❌ Custodial | ✅ Tú tienes la seed |
| Sin contraparte | ❌ | ✅ |
| Sin límites | ❌ (depende de ellos) | ✅ (tu nodo, tus reglas) |
| Transacciones privadas | ❌ | ✅ |
| Conexión propia | ❌ | ✅ LNDHub |
| Canales propios | ❌ | ✅ Tú abres los canales |
| Backup | ❌ | ✅ Seed phrase + macaroon |

---

## 6. Comprobación Final

```bash
# 1. Verificar que LND responde
lncli --rpcserver=localhost:10009 getinfo

# 2. Verificar LNBits + LNDHub
curl -s http://localhost:8000/lndhub/api/v1/info

# 3. Probar conexión BlueWallet
# (escanear QR generado desde LNBits)

# 4. Verificar wallet soberana
lncli --rpcserver=localhost:10009 walletbalance
```

---

*∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ*
*Configuración LNDHub para BlueWallet · Catedral QCAL*
*Nuremberg, 20/Jun/2026*
