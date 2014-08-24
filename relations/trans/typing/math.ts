module typing/math

imports

	include/Relations
	trans/naming/names

type rules
	
	Addition(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and (x-ty == Int() or x-ty == String()) else error  $[Type mismatch: expected Int or String got [x-ty] in Addition] on x
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Addition] on y
		
	Multiplication(x, y)
+	Division(x, y)
+	Modulo(x, y)
+	Subtraction(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == Int() else error $[Type mismatch: expected Int got [x-ty] in Math Operation] on x
		and	y-ty == Int() else error $[Type mismatch: expected Int got [y-ty] in Math Operation] on y
		
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
		and	((not y => Int(j) or y => Int(i) and i == "0") // might be division by zero
					and <lowerbound-zero> mu1 => mu
			 or	y => Int(k) and (not k == "0")                 // divided by a constant not zero
					and mu1 => mu)
		and (x-mu == ZeroOrOne() or x-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [x-mu] in Math Operation] on x
		and (y-mu == ZeroOrOne() or y-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [y-mu] in Math Operation] on y

