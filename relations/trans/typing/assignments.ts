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
		and	a-ty == val-ty	else error $[Type mismatch: expected [a-ty] got [val-ty] in Attribute Assignment] on val

	RoleValue(r, val) :-
	where	r		: r-ty
		and	val	: val-ty
		and	r-ty == val-ty else error $[Type mismatch: expected [r-ty] got [val-ty] in Role Assignment] on val

	Attribute(a, a-ty, a-mu, Derivation(e, derivationType)) :-
	where	e	: e-ty
		and	e-ty == a-ty else error $[Type mismatch: expected [a-ty] got [e-ty] in Derivation] on e
			
	Attribute(a, a-ty, a-mu, Derivation(e, derivationType)) :-
	where	e has multiplicity e-mu
		and e-mu == a-mu else error $[Multiplicity mismatch: expected [a-mu] got [e-mu] in Derivation] on e