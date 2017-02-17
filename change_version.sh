grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "0.5.1(.qualifier|-SNAPSHOT)" * | xargs sed -i "" "s/0.5.1/0.6.1/g"
