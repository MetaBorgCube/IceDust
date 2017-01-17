grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml} "http://tinyurl.com/spoofax-eclipse-2-1-0" search . | xargs sed -i "" "s/http:\/\/tinyurl.com\/spoofax-eclipse-2-1-0/http:\/\/download.spoofax.org\/update\/nightly\//g"
grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --include=*.{yaml,xml} "2.1.0" search . | xargs sed -i "" "s/2.1.0/2.2.0-SNAPSHOT/g"
