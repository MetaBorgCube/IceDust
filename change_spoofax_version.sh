FROMVERSION=2.2.0
TOVERSION=2.2.1

grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}" * | xargs sed -i "" "s/${FROMVERSION}/${TOVERSION}/g"
