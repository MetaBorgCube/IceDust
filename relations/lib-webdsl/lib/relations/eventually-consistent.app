module lib/relations/eventually-consistent

section pages

  page flagalldirty() {
    title{ "Eventually Consistent Derived Values - Flag All Dirty" }
    init{
      log("Flag all dirty");
      flagAllDirty();
      log("Flag all dirty done");
      return root();
    }
  }
  
  page flagdirty(entity:String, attribute:String) {
    title{ "Eventually Consistent Derived Values - Flag Dirty" }
    init{
      log("Flag dirty " + entity + "." + attribute);
      flagDirty(entity, attribute);
      log("Flag dirty " + entity + "." + attribute + " done");
      return root();
    }
  }

  page enableupdates() {
    title{ "Eventually Consistent Derived Values - Enable Updates" }
    init{
      enableUpdates();
      return root();
    }
  }

  page disableupdates() {
    title{ "Eventually Consistent Derived Values - Disable Updates" }
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

section queue

  native class java.util.Queue as Queue{
    offer(String) : Bool
    add(String) : Bool
    addAll(List<String>) : Bool
    poll() : String
    contains(String) : Bool
    isEmpty() : Bool
  }
