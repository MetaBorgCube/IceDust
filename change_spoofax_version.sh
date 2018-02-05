FROMVERSION=2.3.0
TOVERSION=2.4.0

grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}" . | xargs sed -i "" "s/${FROMVERSION}/${TOVERSION}/g"
