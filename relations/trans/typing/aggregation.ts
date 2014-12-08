module typing/aggregation

imports
	
	include/Relations
	trans/naming/names
	
	lib/types/-

type rules

	Min(x)
+	Max(x)
+ Sum(x)
+	Avg(x) : x-ty
	where	x	: x-ty
		and x-ty == Int() else error $[Type mismatch: expected Int got [x-ty] in Aggregation] on x

  Conj(x)
+	Disj(x) : x-ty
	where	x	: x-ty
		and x-ty == Boolean() else error $[Type mismatch: expected Boolean got [x-ty] in Aggregation] on x

	Concat(x) : x-ty
	where x : x-ty
		and x-ty == String() else error $[Type mismatch: expected String got [x-ty] in Concatenation] on x

	Count(x) : Int()


	Min(x)
+	Max(x)
+	Avg(x)
+ Conj(x)
+ Disj(x)
+ Concat(x) has multiplicity mu
	where x has multiplicity x-mu
		and <upperbound-one> (x-mu) => mu
		and (x-mu == ZeroOrMore() or x-mu == OneOrMore())	else error "Expected multiplicity of higher than One" on x

	Sum(x)
+	Count(x) has multiplicity One()
