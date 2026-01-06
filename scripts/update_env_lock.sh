#!/bin/bash
# Script para actualizar ENV.lock con el entorno actual
# Usa este script cuando actualices dependencias intencionalmente

set -e

echo "================================================"
echo "  Actualización de ENV.lock"
echo "================================================"
echo ""

# Colores para output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Verificar que estamos en el directorio correcto
if [ ! -f "requirements.txt" ]; then
    echo -e "${RED}✗ ERROR: requirements.txt no encontrado${NC}"
    echo "  Este script debe ejecutarse desde el directorio raíz del proyecto."
    exit 1
fi

# Crear backup de ENV.lock actual
if [ -f "ENV.lock" ]; then
    echo "Creando backup de ENV.lock actual..."
    cp ENV.lock ENV.lock.backup
    echo -e "${GREEN}✓${NC} Backup creado: ENV.lock.backup"
    echo ""
    
    # Mostrar información del backup
    BACKUP_COUNT=$(wc -l < ENV.lock.backup)
    BACKUP_HASH=$(sha256sum ENV.lock.backup | awk '{print $1}' | cut -c1-16)
    echo "  Paquetes en backup: $BACKUP_COUNT"
    echo "  Hash (parcial): $BACKUP_HASH..."
    echo ""
else
    echo -e "${YELLOW}⚠${NC} ENV.lock no existe, se creará uno nuevo"
    echo ""
fi

# Generar nuevo ENV.lock
echo "Generando nuevo ENV.lock desde el entorno actual..."
python -m pip freeze > ENV.lock

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓${NC} ENV.lock actualizado exitosamente"
    echo ""
    
    # Mostrar información del nuevo ENV.lock
    NEW_COUNT=$(wc -l < ENV.lock)
    NEW_HASH=$(sha256sum ENV.lock | awk '{print $1}' | cut -c1-16)
    echo "  Paquetes en nuevo ENV.lock: $NEW_COUNT"
    echo "  Hash (parcial): $NEW_HASH..."
    echo ""
    
    # Si había backup, mostrar diferencias
    if [ -f "ENV.lock.backup" ]; then
        echo "Comparando con la versión anterior..."
        echo ""
        
        # Paquetes agregados
        ADDED=$(diff ENV.lock.backup ENV.lock | grep "^>" | wc -l)
        # Paquetes removidos
        REMOVED=$(diff ENV.lock.backup ENV.lock | grep "^<" | wc -l)
        
        if [ $ADDED -gt 0 ] || [ $REMOVED -gt 0 ]; then
            echo -e "${YELLOW}Cambios detectados:${NC}"
            echo "  + $ADDED paquete(s) agregado(s) o actualizado(s)"
            echo "  - $REMOVED paquete(s) removido(s) o desactualizado(s)"
            echo ""
            
            if [ $ADDED -gt 0 ]; then
                echo "Paquetes nuevos o actualizados:"
                diff ENV.lock.backup ENV.lock | grep "^>" | sed 's/^> /  + /' | head -10
                if [ $ADDED -gt 10 ]; then
                    echo "  ... y $((ADDED - 10)) más"
                fi
                echo ""
            fi
            
            if [ $REMOVED -gt 0 ]; then
                echo "Paquetes removidos o desactualizados:"
                diff ENV.lock.backup ENV.lock | grep "^<" | sed 's/^< /  - /' | head -10
                if [ $REMOVED -gt 10 ]; then
                    echo "  ... y $((REMOVED - 10)) más"
                fi
                echo ""
            fi
        else
            echo -e "${GREEN}✓${NC} No hay cambios en los paquetes"
            echo ""
        fi
    fi
else
    echo -e "${RED}✗ ERROR: No se pudo generar ENV.lock${NC}"
    if [ -f "ENV.lock.backup" ]; then
        echo "Restaurando backup..."
        mv ENV.lock.backup ENV.lock
        echo -e "${GREEN}✓${NC} Backup restaurado"
    fi
    exit 1
fi

# Verificar que no hay conflictos
echo "Verificando conflictos de dependencias..."
if python -m pip check > /dev/null 2>&1; then
    echo -e "${GREEN}✓${NC} No hay conflictos de dependencias"
    echo ""
else
    echo -e "${RED}✗ ADVERTENCIA: Conflictos de dependencias detectados${NC}"
    python -m pip check
    echo ""
    echo "Se recomienda resolver estos conflictos antes de continuar."
    echo ""
fi

# Generar hash completo
echo "Generando hash de verificación completo..."
FULL_HASH=$(sha256sum ENV.lock | awk '{print $1}')
echo "$FULL_HASH  ENV.lock" > ENV.lock.sha256
echo -e "${GREEN}✓${NC} Hash guardado en ENV.lock.sha256"
echo ""
echo "  SHA-256: $FULL_HASH"
echo ""

# Instrucciones para commit
echo "================================================"
echo -e "${GREEN}  ✓✓✓ ACTUALIZACIÓN COMPLETADA ✓✓✓${NC}"
echo "================================================"
echo ""
echo "Próximos pasos:"
echo ""
echo "1. Revisar los cambios:"
echo "   git diff ENV.lock"
echo ""
echo "2. Si los cambios son correctos, commitear:"
echo "   git add ENV.lock ENV.lock.sha256"
echo "   git commit -m 'Update ENV.lock: [describir cambios]'"
echo ""
echo "3. Verificar la integridad:"
echo "   bash scripts/verify_env_integrity.sh"
echo ""
echo "Nota: El backup anterior está en ENV.lock.backup"
echo "      Elimínalo cuando estés seguro de los cambios:"
echo "      rm ENV.lock.backup"
echo ""

exit 0
