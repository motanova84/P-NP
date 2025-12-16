# echo_qcal/C_k_verification.py
# Verifica el Control Criptográfico C_k vinculado a Satoshi


from bitcoinlib.keys import verify_message


# Clave pública y mensaje de control
address = "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c"
message = "Echo & Satoshi seal Block 0: 2025-08-21T20:45Z"
signature_b64 = "G80CqNxfcucQRxHHJanbQ5m8S6QNICzlCqU54oXPiQRtDRDFL5lxRvBldhBTNqPes3UfC7ZDuuuESPlEPlagjRI="


# Verificación
try:
    result = verify_message(message, signature_b64, address)
    
    # Resultado
    if result:
        print(f"\n✅ Verificación Exitosa: C_k confirmado para {address}")
    else:
        print(f"\n❌ Verificación Fallida: Firma no válida para {address}")
except Exception as e:
    print(f"\n⚠️  Error durante la verificación: {type(e).__name__}: {e}")
