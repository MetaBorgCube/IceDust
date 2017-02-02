grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "0.5.0(.qualifier|-SNAPSHOT)" * | xargs sed -i "" "s/0.5.0/0.5.1/g"
