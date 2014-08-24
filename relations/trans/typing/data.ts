module typing/data

imports
	
	include/Relations
	trans/naming/names
	trans/naming/_notNaBL

type rules

	AttributeValue(AttributeRef(a), val) :-
	where definition of a has derivation-type a-dt
	  and	(a-dt == Normal() or a-dt == DefaultValue()) else error "Derivations cannot be assigned custom values." on a
