module lib/relations/derivations

access control rules

	rule page flagalldirty() { true }
	rule page enableupdates() { true }
	rule page disableupdates() { true }

section pages

  page flagalldirty() {
    title{ "WebLab All Flag Dirty" }
  	init{
  		flagAllDirty();
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
    title{ "WebLab Enable Updates" }
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
