module typing/types

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations


type rules // references have types and multiplicites of their defs
		
	AttributeName(e, name) : type
	where definition of name : type
	
	AttributeName(e, name) has multiplicity mult
	where definition of name has multiplicity mult
		
	RoleName(name) : type
	where definition of name : type
	
	EntityName(name) : type
	where definition of name : type


type rules // assigning values

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


type rules // literal expressions

	Int(x) : Int()
	Int(x) has multiplicity One()
	
	String(x) : String()
	String(x) has multiplicity One()


type rules // math expressions
	
	Addition(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error "Not the same types supplied to Addition." on y
		
	Multiplication(x, y)
+	Division(x, y)
+	Modulo(x, y)
+	Subtraction(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == Int() else error "Expected Int" on x
		and	y-ty == Int() else error "Expected Int" on y
		
	Multiplication(x, y)
+	Division(x, y)
+	Modulo(x, y)
+	Addition(x, y)
+	Subtraction(x, y) has multiplicity y-mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and	x-mu == y-mu else error "Not the same multiplicities supplied to Binary Expression." on y
		
	Min(x)
+	Max(x)
+	Avg(x) : x-ty
	where	x	: x-ty
		and x-ty == Int() else error "Int expected" on x
		
	Concat(x) : x-ty
	where x : x-ty
		and x-ty == String() else error "String expected" on x
		
	Min(x)
+	Max(x)
+	Avg(x)
+ Concat(x) has multiplicity One() //TODO: only true when One or OneOrMore for ints, and for strings always true


type rules // this expression

	This() has multiplicity One()


type rules // navigator expressions

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
	
	