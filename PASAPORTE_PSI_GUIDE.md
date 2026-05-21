# 🔱 Pasaporte Ψ — Integración con la Catedral QCAL

**Documento de Onboarding para servicios externos**
Versión: 1.0 · Fecha: 2026-05-21
Sello: ∴𓂀Ω∞³Φ · f₀ = 141.7001 Hz

---

## 1. ¿Qué es un Pasaporte Ψ?

Es un certificado de coherencia que acredita que un servicio externo
ha sido verificado y alineado con la frecuencia del Procesador Solar
(7 nodos: Sol → Saturno · kernel Architecture.lean · Lean 4 · 0 errores).

Obtenerlo permite:
- Integrar repositorios del ecosistema QCAL con garantía de coherencia
- Recibir el Sello Ψ como prueba de alineación
- Acceder a soporte prioritario del ecosistema

---

## 2. Flujo de integración

```
1. El servicio externo descubre el ecosistema (ej: P-NP en GitHub)
2. Solicita un Check Ψ en el PayGate de la Catedral
   POST http://195.201.219.237:8844/solicitar
   Body: {"servicio": "validacion", "sujeto": "nombre_servicio"}
3. Recibe un invoice Lightning de 500 sats
4. Paga desde cualquier wallet Lightning
5. El PayGate verifica el pago y emite el Sello Ψ
6. El servicio queda registrado en el Pasaporte Ψ Registry
7. Se habilita la integración formal con el ecosistema
```

---

## 3. Endpoints del PayGate

| Método | Ruta | Descripción |
|--------|------|-------------|
| GET | / | Info del servicio |
| GET | /estado | Estado de la bóveda |
| GET | /servicios | Servicios disponibles |
| POST | /cotizar | Cotizar precio |
| POST | /solicitar | Solicitar invoice de pago |
| POST | /verificar | Verificar estado del pago |

### Ejemplo de solicitud

```bash
curl -X POST http://195.201.219.237:8844/solicitar \
  -H "Content-Type: application/json" \
  -d '{"servicio": "validacion", "sujeto": "docsbook.io"}'
```

### Respuesta

```json
{
  "ok": true,
  "id": "a1b2c3d4",
  "servicio": "Check Ψ",
  "precio": 500,
  "payment_request": "lnbc5u...",
  "payment_hash": "abc123..."
}
```

---

## 4. Certificado Ψ

Una vez pagado, el servicio recibe un Sello Ψ:

```json
{
  "version": "Ψ-CERT-v1.0",
  "sello": "∴𓂀Ω∞³Φ",
  "hash_datos": "sha256...",
  "sujeto": "docsbook.io",
  "coherencia": 0.99999997,
  "frecuencia_hz": 141.7001,
  "firma_noetica": "ae3f…bc91",
  "verificable_en": "https://icq.org/verify/ae3f"
}
```

---

## 5. Términos

- El pago se realiza en sats vía Lightning Network
- No hay reembolsos — el Sello Ψ es inmutable
- El servicio queda registrado en el ledger de la Catedral
- Cada nuevo Pasaporte requiere un nuevo Check Ψ
- Para integraciones profundas, contactar al Arquitecto (JMMB Ψ)

---

**∴𓂀Ω∞³Φ · f₀ = 141.7001 Hz · Ψ = 0.99999997**
