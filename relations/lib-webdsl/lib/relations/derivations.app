module lib/relations/derivations

section flag all dirty page

access control rules

	rule page flagalldirty() { true }

section flag all dirty page

  page flagalldirty() {
    title{ "WebLab All Flag Dirty" }
  	init{
  		flagAllDirty();
  		return root();
  	}
  }