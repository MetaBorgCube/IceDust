grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml,MF} "0.6.1(.qualifier|-SNAPSHOT)" * | xargs sed -i "" "s/0.6.1/0.6.2/g"
