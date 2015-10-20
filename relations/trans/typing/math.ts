module typing/math

imports

	// constructors
	src-gen/signatures/Expressions-sig
	src-gen/signatures/Types-sig
	
	// functions
	typing/_multiplicity-functions
	trans/naming/names
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

type rules
	
	Addition(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and (x-ty == Int() or x-ty == Float() or x-ty == String()) else error  $[Type mismatch: expected Int or String got [x-ty] in Addition] on x
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Addition] on y
		
	Subtraction(x, y) : ty
	where	x	: x-ty
		and	y	: y-ty
		and	(x-ty == Int() or x-ty == Float() or x-ty == Datetime()) else error $[Type mismatch: expected Int, String or Datetime got [x-ty] in Math Operation] on x
		and	x-ty == y-ty else error $[Type mismatch: expected Int got [y-ty] in Math Operation] on y
		and ((x-ty == Int() or x-ty == Float()) and x-ty => ty or
		     (x-ty == Datetime() and               Int() => ty))
		
	Multiplication(x, y)
+	Division(x, y)
+	Modulo(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and	(x-ty == Int() or x-ty == Float()) else error $[Type mismatch: expected Int got [x-ty] in Math Operation] on x
		and	x-ty == y-ty else error $[Type mismatch: expected Int got [y-ty] in Math Operation] on y
		
	Multiplication(x, y)
+	Addition(x, y)
+	Subtraction(x, y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and <cartesian-product> (x-mu, y-mu) => mu
		and (x-mu == ZeroOrOne() or x-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [x-mu] in Math Operation] on x
		and (y-mu == ZeroOrOne() or y-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [y-mu] in Math Operation] on y

	Division(x, y)
+	Modulo(x, y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and <cartesian-product> (x-mu, y-mu) => mu1
		and	((not (y => Int(j) or y => Float(j2)) or y => Int(i) and i == "0" or y => Float(f) and f == "0.0") // might be division by zero
					and <lowerbound-zero> mu1 => mu
			 or	y => Int(k) and (not k == "0")                 // divided by a constant not zero
					and mu1 => mu
			 or y => Float(l) and (not l == "0.0")             // divided by a constant not zero TODO: also catch 0.00 00.00 etc
			 		and mu1 => mu
				)
		and (x-mu == ZeroOrOne() or x-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [x-mu] in Math Operation] on x
		and (y-mu == ZeroOrOne() or y-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [y-mu] in Math Operation] on y

	Multiplication(x, y)
+	Addition(x, y)
+	Subtraction(x, y)
+	Division(x, y)
+	Modulo(x, y) has ordering or
	where	x	has ordering x-or
		and	y	has ordering  y-or
		and <or-nav> (x-or, y-or) => or
		