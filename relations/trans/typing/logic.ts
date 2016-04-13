module typing/logic

imports

	// constructors
	src-gen/signatures/Expressions-sig
	src-gen/signatures/Types-sig	 
	trans/api/constructors
	
	// functions
	typing/_multiplicity-functions
  names/naming/names
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

type rules
	
	Not(x) : Boolean()
	where x : x-ty
		and (x-ty == Boolean() or x-ty <sub: Boolean())
		    else error $[Type mismatch: expected Boolean got [x-ty] in Not] on x
	
	LessThan(x, y)
+	LessThanEqual(x, y)
+	GreaterThan(x, y)
+	GreaterThanEqual(x, y) : Boolean()
	where	x	: x-ty
    and y : y-ty
		and (x-ty == Int() or x-ty == Float() or x-ty == String() or x-ty == Datetime())
		    else error $[Type mismatch: expected Int, Float, String or Datetime got [x-ty] in Comparison] on x
    and <least-upper-bound>(x-ty, y-ty) => lup-ty
		    else error $[Type mismatch: expected [x-ty] got [y-ty] in Comparison] on y

	Equal(x, y)
+	Inequal(x, y) : Boolean()
	where	x	: x-ty
		and	y	: y-ty
    and <least-upper-bound>(x-ty, y-ty) => lup-ty
        else error $[Type mismatch: expected [x-ty] got [y-ty] in Comparison] on y

	And(x, y)
+	Or(x, y) : Boolean()
	where	x	: x-ty
		and	y	: y-ty
    and (x-ty == Boolean() or x-ty <sub: Boolean())
        else error $[Type mismatch: expected Boolean got [x-ty] in Logic Operation] on x
    and (y-ty == Boolean() or y-ty <sub: Boolean())
        else error $[Type mismatch: eypected Boolean got [y-ty] in Logic Operation] on y
	
	If(x, y, z) : ty
	where x : x-ty
		and y : y-ty
		and z : z-ty
		and (x-ty == Boolean() or x-ty <sub: Boolean())
		    else error $[Type mismatch: expected Boolean got [x-ty] in Contional] on x
    and <least-upper-bound>(y-ty, z-ty) => ty
        else error $[Type mismatch: expected [y-ty] got [z-ty] in Contional] on z


	Not(x) has multiplicity x-mu
	where x has multiplicity x-mu

	LessThan(x, y)
+	LessThanEqual(x, y)
+	GreaterThan(x, y)
+	GreaterThanEqual(x, y)
+	Equal(x, y)
+	Inequal(x, y)
+	And(x, y)
+	Or(x, y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and <cartesian-product> (x-mu, y-mu) => mu
		and (x-mu == ZeroOrOne() or x-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [x-mu] in Math Operation] on x
		and (y-mu == ZeroOrOne() or y-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [y-mu] in Math Operation] on y

	If(x, y, z) has multiplicity mu
	where x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and z	has multiplicity z-mu
		and <cartesian-product> (z-mu, y-mu) => mu
		and (x-mu == One()) else error $[Multiplicity mismatch: expected One got [x-mu] in Conditional] on x

	Not(x) has ordering x-or
	where x has ordering x-or

	LessThan(x, y)
+	LessThanEqual(x, y)
+	GreaterThan(x, y)
+	GreaterThanEqual(x, y)
+	Equal(x, y)
+	Inequal(x, y)
+	And(x, y)
+	Or(x, y) has ordering or
	where	x	has ordering x-or
		and	y	has ordering  y-or
		and <or-nav> (x-or, y-or) => or
		
	If(x, y, z) has ordering or
	where	x	has ordering x-or
		and	y	has ordering  y-or
		and	z	has ordering  z-or
		and <or-nav> (x-or, y-or) => or2
		and <or-nav> (or2, z-or) => or
		