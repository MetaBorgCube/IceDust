FROMVERSION=0.6.3
TOVERSION=0.7.0

grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}.qualifier" * | xargs sed -i "" "s/${FROMVERSION}.qualifier/${TOVERSION}/g"
grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "${FROMVERSION}-SNAPSHOT" * | xargs sed -i "" "s/${FROMVERSION}-SNAPSHOT/${TOVERSION}/g"
