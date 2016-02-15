module typing/data

imports

	// constructors
	src-gen/signatures/Data-sig
	src-gen/signatures/Model-sig
	src-gen/signatures/Types-sig	 
	trans/api/constructors
	
	// functions
  names/naming/names
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

type rules

	AttributeValue(AttributeRef(a), val) :-
	where definition of a has derivation-type a-dt
	  and	(a-dt == Normal() or a-dt == DefaultValue()) else error "Derivations cannot be assigned custom values." on a

type rules

  EntityInstance(ei, e, mem) : e-ty
  where definition of ei : e-ty
  
  EntityInstance(ei, e, mem) has multiplicity One()
  
  EntityInstance(ei, e, mem) has ordering Ordered()
	
  EntityInstanceWrapper(ri, ei) : ei-ty
  where ei : ei-ty
	
  EntityInstanceWrapper(ri, ei) has multiplicity One()
  
  EntityInstanceWrapper(ri, ei) has ordering Ordered()
	