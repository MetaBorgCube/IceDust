module typing/logic

imports

	include/Relations
	trans/naming/names

	lib/types/-

type rules
	
	Not(x) : x-ty
	where x : x-ty
		and x-ty == Boolean() else error $[Type mismatch: expected Boolean got [x-ty] in Not] on x
	
	LessThan(x, y)
+	LessThanEqual(x, y)
+	GreaterThan(x, y)
+	GreaterThanEqual(x, y) : Boolean()
	where	x	: x-ty
		and (x-ty == Int() or x-ty == String()) else error $[Type mismatch: expected Int or String got [x-ty] in Comparison] on x
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Comparison] on y

	Equal(x, y)
+	Inequal(x, y) : Boolean()
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Comparison] on y

	And(x, y)
+	Or(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == Boolean() else error $[Type mismatch: expected Boolean got [x-ty] in Logic Operation] on x
		and	y-ty == Boolean() else error $[Type mismatch: expected Boolean got [y-ty] in Logic Operation] on y
	
	TernaryConditional(x, y, z) : y-ty
	where x : x-ty
		and y : y-ty
		and z : z-ty
		and x-ty == Boolean() else error $[Type mismatch: expected Boolean got [x-ty] in Contional] on x
		and y-ty == z-ty else error $[Type mismatch: expected [y-ty] got [z-ty] in Conditional] on z


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

	TernaryConditional(x, y, z) has multiplicity mu
	where x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and z	has multiplicity z-mu
		and <cartesian-product> (x-mu, y-mu) => mu1
		and <cartesian-product> (z-mu, mu1) => mu
		and (x-mu == ZeroOrOne() or x-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [x-mu] in Math Operation] on x
		and (y-mu == ZeroOrOne() or y-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [y-mu] in Math Operation] on y
		and (z-mu == ZeroOrOne() or z-mu == One()) else error $[Multiplicity mismatch: expected One or ZeroOrOne got [z-mu] in Math Operation] on z

