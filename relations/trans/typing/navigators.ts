module typing/navigators

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations

type rules

	NavigateIn(This(), nav, into, EntityType(rel-ty)) : rel-ty
	where into 	: into-ty
	
	NavigateOut(This(), nav, EntityType(rel-ty), out) : out-ty
	where	out		: out-ty

	NavigateIn(prev, nav, into, EntityType(rel-ty)) : rel-ty
	where prev	: prev-ty
		and into	: into-ty
		and prev-ty == into-ty else error "The inRole is of the wrong type." on into
	
	NavigateIn(prev, nav, into, EntityType(rel-ty)) has multiplicity into-mu	//TODO: this is only true of prev has multiplicity of One()
	where prev has multiplicity prev-mu
		and definition of into has multiplicity into-mu
	
	NavigateOut(prev, nav, EntityType(rel-ty), out) : out-ty
	where	out		: out-ty
		and prev	: prev-ty
		and rel-ty == prev-ty	else error "The relation is of the wrong type." on rel-ty
		
	NavigateOut(prev, nav, EntityType(rel-ty), out) has multiplicity prev-mu
	where prev has multiplicity prev-mu
