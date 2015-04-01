module typing/assignments

imports

	// constructors
	src-gen/signatures/Data-sig
	src-gen/signatures/Model-sig
	src-gen/signatures/Rules-sig
	src-gen/signatures/Types-sig
	trans/api/constructors
	trans/desugaring/constructors
	
	// functions
	typing/_multiplicity-functions
	trans/naming/names
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

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

	LHSEdge(e, n)
+	NHSEdge(e, n)
+	RHSEdge(e, n) :-
	where	e : e-ty
		and n : n-ty
		and e-ty == n-ty else error $[Type mismatch: expected [e-ty] got [n-ty] in Edge] on n

	LHSNodeDefByType(n, None(), v)
+	NHSNodeDefByType(n, None(), v)
+	RHSNodeDefByType(n, None(), v) :-
	where "0" == "1" else error $[No Type given for [n]] on n

	LHSNode(n, EntityRef(e-ty), None())
+	NHSNode(n, EntityRef(e-ty), None())
+	RHSNode(n, EntityRef(e-ty), None()) :-
	where definition of n : n-ty
		and n-ty == e-ty else error $[Type mismatch: expected [n-ty] got [e-ty]] on e-ty

	Attr(AttrRef(a), val) :-
	where	definition of a : a-ty
		and	val	: val-ty
		and	a-ty == val-ty	else error $[Type mismatch: expected [a-ty] got [val-ty] in Attribute Value] on val


