FROMNAME=icedust2
TONAME=icedust
FROMEXTENSION=ice2
TOEXTENSION=ice

# change name
grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --exclude=*change_name.sh* --exclude=*_subtyping.ts* --exclude=*_runtime.str* "${FROMNAME}" * | xargs sed -i "" "s/${FROMNAME}/${TONAME}/g"
find . -depth -name "*${FROMNAME}*" -execdir sh -c "mv {} \$(echo {} | sed \"s/${FROMNAME}/${TONAME}/\")" \;

# change extension
grep -rEl --exclude=*/target/* --exclude=*/src-gen/* --exclude=*change_name.sh* --exclude=*_subtyping.ts* --exclude=*_runtime.str* "extensions : ${FROMEXTENSION}" * | xargs sed -i "" "s/extensions : ${FROMEXTENSION}/extensions : ${TOEXTENSION}/g"
find . -depth -name "*.${FROMEXTENSION}*" -execdir sh -c "mv {} \$(echo {} | sed \"s/.${FROMEXTENSION}/.${TOEXTENSION}/\")" \;
