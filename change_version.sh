FROMVERSION=0.7.1
TOVERSION=0.7.2

grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}(.qualifier|-SNAPSHOT)" * | xargs sed -i "" "s/${FROMVERSION}/${TOVERSION}/g"
