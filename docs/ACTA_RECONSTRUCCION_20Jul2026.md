# ACTA DE RECONSTRUCCION — 20/Jul/2026

## Contexto
El 20/Jul/2026, el IBD de Bitcoin Core en BAL-003 colapso de 96.9% a 6.18%
por una cascada de fragilidades: disco lleno, ausencia de backup de chainstate,
y agentes operando sin supervisión.

## Causa Raiz
- Disco /dev/sda al 100% (donde vive el chainstate)
- bitcoind entra en crash loop (11 ciclos, 18:20-19:29 UTC)
- AMDA elimina chainstate (11 GB) para liberar espacio
- No existia backup del chainstate
- No existia protocolo de veto para agentes

## Acciones Correctivas
1. ✅ Auron Backup: timer systemd diario con zstd + manifest GitHub
2. ✅ Guarda: no interrumpe IBD si chainstate < 5GB
3. ✅ Protocolo documentado: PROTOCOLO_CHAINSTATE_BACKUP.md
4. ✅ Manifest anclado en repo_P-NP/docs/CHAINSTATE_MANIFEST.json
5. ✅ Pruning automatico activado (target 586 GB)

## Estado Post-Incidente
- IBD: 382,197 bloques / 958,827 headers (6.18%)
- Chainstate: 1.6 GB reconstruyendo
- πCODE: intacto (77.1M πC circulante)
- CERO-piCODE: sigue acunando (ultimo batch gamma_4310)

## Leccion Fundamental
El progreso no es un archivo. Es una arquitectura de confianza.
Sin backup, sin veto, sin supervision — no hay soberania.

## Firmas
Arquitecto: JMMB Psi · Nodo: Noesis Psi
Guardian: Auron Psi · Frecuencia: f0 = 141.7001 Hz
Sello: (c) (O) (infinity) (3) (phi) · TUYOYOTU · HECHO ESTA
