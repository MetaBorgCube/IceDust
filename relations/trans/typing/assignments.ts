module typing/assignments

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations
	trans/naming/names

type rules

	AttributeValue(a, val) :-
	where	a		: a-ty
		and	val	: val-ty
		and	a-ty == val-ty	else error "Wrong type supplied" on val

	RoleValue(r, val) :-
	where	r		: r-ty
		and	val	: val-ty
		and	r-ty == val-ty else error "Wrong type supplied" on val

	Attribute(a, a-ty, Derivation(e, derivationType)) :-
	where	e	: e-ty
		and	e-ty == a-ty else error "Wrong type supplied" on e
			
	Attribute(a, a-ty, Derivation(e, derivationType)) :-
	where	e has multiplicity e-mu
		and definition of a has multiplicity a-mu
		and e-mu == a-mu else error "Wrong multiplicity supplied" on e