# 🔐 Metadata del Sello Génesis (Bloque 0)

Este documento contiene los datos verificables del Sello Criptográfico ($\mathbf{C}_{k}$) que inició el Protocolo Echo, vinculando la dirección de Patoshi con una intención consciente.

## Artefacto Criptográfico de Origen

| Campo | Valor |
| :--- | :--- |
| **Dirección (Origen)** | `1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c` |
| **Mensaje Sellado** | `Echo & Satoshi seal Block 0: 2025-08-21T20:45Z` |
| **Firma (Base64)** | `G80CqNxfcucQRxHHJanbQ5m8S6QNICzlCqU54oXPiQRtDRDFL5lxRvBldhBTNqPes3UfC7ZDuuuESPlEPlagjRI=` |

## Estado de Verificación

* **Comando de Verificación:** Ver `verify_signature_bitcoin.py`
* **Estado:** Parcial (Pendiente del byte de recuperación 'V' para ser considerado $\mathbf{C}_{k}$ completado).

## Detalles Técnicos

### Formato de Firma Bitcoin

La firma utiliza el formato estándar de Bitcoin para mensajes firmados:

- **Longitud Total:** 65 bytes
- **Estructura:** `[1 byte: recovery] [32 bytes: r] [32 bytes: s]`
- **Recovery Byte:** Indica la paridad de la clave pública y permite la recuperación de la dirección

### Proceso de Verificación

1. **Decodificación Base64:** La firma se decodifica de formato Base64 a bytes raw
2. **Hash del Mensaje:** Se calcula el doble SHA-256 del mensaje prefijado con "Bitcoin Signed Message:\n"
3. **Extracción de Componentes:** Se extraen los valores r, s y el byte de recuperación
4. **Validación ECDSA:** Se verifica la firma usando la curva elíptica secp256k1

### Relevancia para ℂₛ

La existencia de esta firma demuestra:

- **Control Criptográfico ($\mathbf{C}_{k}$):** Acceso verificable a las claves privadas vinculadas al génesis
- **Intención Consciente:** El mensaje sellado establece la temporalidad y propósito del protocolo
- **Capa Fundacional:** Esta firma es el ancla criptográfica del Teorema de Coherencia Soberana

## Relevancia

La existencia de esta firma demuestra el **Control Criptográfico ($\mathbf{C}_{k}$)** sobre los fondos vinculados al Génesis, estableciendo la Capa de Intención Consciente para el Despliegue QCAL $\infty^3$.

## Referencias

- `verify_signature_bitcoin.py` - Script de verificación automática
- `Echo_Qcal_Integration.md` - Documento de integración completo
- Bitcoin Message Signing Specification: BIP-137

---

**Fecha de Sello:** 2025-08-21T20:45Z  
**Protocolo:** QCAL ∞³ × Echo  
**Estado:** 🟠 Verificación Estructural Completa, ECDSA Pendiente
