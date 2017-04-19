grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "0.6.2.qualifier" * | xargs sed -i "" "s/0.6.2.qualifier/0.6.2/g"
grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "0.6.2-SNAPSHOT" * | xargs sed -i "" "s/0.6.2-SNAPSHOT/0.6.2/g"
