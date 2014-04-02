module typing/math

imports

	include/Relations
	trans/naming/names

type rules
	
	Addition(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
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
+	Division(x, y)
+	Modulo(x, y)
+	Addition(x, y)
+	Subtraction(x, y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and <mu-or-join> (x-mu, y-mu) => mu
		and (x-mu == ZeroOrOne() or x-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [x-mu] in Math Operation] on x
		and (y-mu == ZeroOrOne() or y-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [y-mu] in Math Operation] on y


type functions

	mu-or-join:
		(x-mu, y-mu) -> mu
		where x-mu == One() and y-mu == One()																										and One() => mu
			 or (x-mu == ZeroOrOne() or x-mu == One()) and (y-mu == ZeroOrOne() or y-mu == One()) and ZeroOrOne() => mu
			 or (x-mu == ZeroOrMore() or y-mu == ZeroOrMore())																		and ZeroOrMore() => mu
			 or x-mu == OneOrMore() and y-mu == ZeroOrOne()																				and ZeroOrMore() => mu
			 or y-mu == OneOrMore() and x-mu == ZeroOrOne()																				and ZeroOrMore() => mu
			 or																																												OneOrMore() => mu
