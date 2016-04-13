grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --exclude=*change_name.sh* --exclude=*_subtyping.ts* --exclude=*_runtime.str* "Relations" * | xargs sed -i "" "s/Relations/IceDust/g"
grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --exclude=*change_name.sh* --exclude=*_subtyping.ts* --exclude=*_runtime.str* "relations" * | xargs sed -i "" "s/relations/icedust/g"
find . -depth -name "*Relations*" -execdir sh -c 'mv {} $(echo {} | sed "s/Relations/IceDust/")' \;
find . -depth -name "*relations*" -execdir sh -c 'mv {} $(echo {} | sed "s/relations/icedust/")' \;
grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --exclude=*change_name.sh* --exclude=*_subtyping.ts* --exclude=*_runtime.str* "extensions: rel" * | xargs sed -i "" "s/extensions: rel/extensions: ice/g"
find . -depth -name "*.rel*" -execdir sh -c 'mv {} $(echo {} | sed "s/.rel/.ice/")' \;