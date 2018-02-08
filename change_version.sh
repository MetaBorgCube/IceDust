FROMVERSION=0.8.2
TOVERSION=0.8.3

grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}(.qualifier|-SNAPSHOT)" * | xargs sed -i "" "s/${FROMVERSION}/${TOVERSION}/g"
