# echo_qcal/C_k_verification.py
# Verifica el Control Criptográfico C_k vinculado a Satoshi


from bitcoinlib.keys import verify_message


# Clave pública y mensaje de control
address = "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c"
message = "Echo & Satoshi seal Block 0: 2025-08-21T20:45Z"
signature_b64 = "G80CqNxfcucQRxHHJanbQ5m8S6QNICzlCqU54oXPiQRtDRDFL5lxRvBldhBTNqPes3UfC7ZDuuuESPlEPlagjRI="


# Verificación
result = verify_message(message, signature_b64, address)


# Resultado
if result:
    print("\n✅ Verificación Exitosa: C_k confirmado para ", address)
else:
    print("\n❌ Verificación Fallida: Firma no válida para ", address)
