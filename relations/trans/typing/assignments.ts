module typing/assignments

imports
	
	include/Relations
	trans/naming/names

type rules // derivations well-formedness

	Attribute(a, a-ty, a-mu, Derivation(e, derivationType)) :-
	where	e	: e-ty
		and	e-ty == a-ty else error $[Type mismatch: expected [a-ty] got [e-ty] in Derivation] on e
			
	Attribute(a, a-ty, a-mu, Derivation(e, derivationType)) :-
	where	e has multiplicity e-mu
		and (
						a-mu == ZeroOrOne() and e-mu == One()
				 or a-mu == e-mu
				)
		else error $[Multiplicity mismatch: expected [a-mu] got [e-mu] in Derivation] on e

type rules // data well-formedness

	AttributeValue(a, val) :-
	where	a		: a-ty
		and	val	: val-ty
		and	a-ty == val-ty	else error $[Type mismatch: expected [a-ty] got [val-ty] in Attribute Assignment] on val

	RoleValue(r, val) :-
	where	r		: r-ty
		and	val	: val-ty
		and	r-ty == val-ty else error $[Type mismatch: expected [r-ty] got [val-ty] in Role Assignment] on val

type rules // rewrite rules

	Edge(v1, e, v2) :-
	where v2 : v2-ty
		and definition of e : e-ty
		and e-ty == v2-ty else error $[Type mismatch: expected [e-ty] got [v2-ty] in Pattern] on v2
