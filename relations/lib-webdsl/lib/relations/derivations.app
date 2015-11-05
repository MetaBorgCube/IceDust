module lib/relations/derivations

access control rules

  rule page flagalldirty() { true }
  rule page flagdirty(entity:String, attribute:String) { true }
  rule page enableupdates() { true }
  rule page disableupdates() { true }

section pages

  page flagalldirty() {
    title{ "WebLab Flag All Dirty" }
    init{
      log("Flag all dirty");
      flagAllDirty();
      log("Flag all dirty done");
      return root();
    }
  }
  
  page flagdirty(entity:String, attribute:String) {
    title{ "WebLab Flag Dirty" }
    init{
      log("Flag dirty " + entity + "." + attribute);
      flagDirty(entity, attribute);
      log("Flag dirty " + entity + "." + attribute + " done");
      return root();
    }
  }

  page enableupdates() {
    title{ "WebLab Enable Updates" }
    init{
      enableUpdates();
      return root();
    }
  }

  page disableupdates() {
    title{ "WebLab Disable Updates" }
    init{
      disableUpdates();
      return root();
    }
  }

  function enableUpdates ( ) : Void
  {
    log("Enabled updates");
    Settings.setUpdatesEnabled(true);
  }

  function disableUpdates ( ) : Void
  {
    log("Disabled updates");
    Settings.setUpdatesEnabled(false);
  }
  
  function getUpdatesEnabled () : Bool {
    return Settings.getUpdatesEnabled();
  }

  native class derivations.Settings as Settings{
    static getUpdatesEnabled( ): Bool
    static setUpdatesEnabled( Bool ): Void
  }
