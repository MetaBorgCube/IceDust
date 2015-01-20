module typing/data

imports

	// constructors
	src-gen/signatures/Data-sig
	src-gen/signatures/Model-sig
	src-gen/signatures/Types-sig	 
	trans/api/constructors
	
	// functions
	trans/naming/names
	
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
