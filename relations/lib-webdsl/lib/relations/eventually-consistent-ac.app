module lib/relations/eventually-consistent-ac

access control rules

  rule page flagalldirty() { true }
  rule page flagdirty(entity:String, attribute:String) { true }
  rule page enableupdates() { true }
  rule page disableupdates() { true }
