grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "0.6.2(.qualifier|-SNAPSHOT)" * | xargs sed -i "" "s/0.6.2/0.6.3/g"
