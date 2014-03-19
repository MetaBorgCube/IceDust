module typing/navigators

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations
	trans/naming/names

type rules

	NavigateIn(This(), nav, into, EntityType(rel-ty)) : rel-ty
	where into 	: into-ty
	
	NavigateOut(This(), nav, EntityType(rel-ty), out) : out-ty
	where	out		: out-ty

	NavigateIn(prev, nav, into, EntityType(rel-ty)) : rel-ty
	where prev	: prev-ty
		and into	: into-ty
		and prev-ty == into-ty else error $[Type mismatch: expected [prev-ty] got [into-ty] in Navigation] on into
	
	NavigateIn(prev, nav, into, EntityType(rel-ty)) has multiplicity mu
	where prev has multiplicity prev-mu
		and definition of into has multiplicity into-mu
		and <mu-or-join> (prev-mu, into-mu) => mu
	
	NavigateOut(prev, nav, EntityType(rel-ty), out) : out-ty
	where	out		: out-ty
		and prev	: prev-ty
		and rel-ty == prev-ty	else error $[Type mismatch: expected [prev-ty] got [rel-ty] in Navigation] on rel-ty
		
	NavigateOut(prev, nav, EntityType(rel-ty), out) has multiplicity prev-mu
	where prev has multiplicity prev-mu


type functions

	mu-or-join:
		(x-mu, y-mu) -> mu
		where x-mu == One() and y-mu == One()																										and One() => mu
			 or (x-mu == ZeroOrOne() or x-mu == One()) and (y-mu == ZeroOrOne() or y-mu == One()) and ZeroOrOne() => mu
			 or (x-mu == ZeroOrMore() or y-mu == ZeroOrMore())																		and ZeroOrMore() => mu
			 or x-mu == OneOrMore() and y-mu == ZeroOrOne()																				and ZeroOrMore() => mu
			 or y-mu == OneOrMore() and x-mu == ZeroOrOne()																				and ZeroOrMore() => mu
			 or																																												OneOrMore() => mu
		

type rules // give errors on enties in places where relations are expected

	NavigateIn(_, _, _, EntityType(e-ty))
+ NavigateOut(_, _, EntityType(e-ty), _) :-
	where definition of e-ty has entity-or-relation e-er
	  and e-er == RelationType() else error ["Type error: ", e-ty, " is an entity, a relation is expected."] on e-ty
