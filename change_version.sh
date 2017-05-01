FROMVERSION=0.6.3
TOVERSION=0.7.1

grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}(.qualifier|-SNAPSHOT)" * | xargs sed -i "" "s/${FROMVERSION}/${TOVERSION}/g"
