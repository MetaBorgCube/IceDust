FROMVERSION=2.5.0
TOVERSION=2.6.0

grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}" . | xargs sed -i "" "s/${FROMVERSION}/${TOVERSION}/g"
