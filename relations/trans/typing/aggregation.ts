module typing/aggregation

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations
	trans/naming/names

type rules

	Min(x)
+	Max(x)
+	Avg(x) : x-ty
	where	x	: x-ty
		and x-ty == Int() else error $[Type mismatch: expected Int got [x-ty] in Aggregation] on x

	Min(x)
+	Max(x)
+	Avg(x) has multiplicity mu
	where x has multiplicity x-mu
	and (
				x-mu == ZeroOrMore() and ZeroOrOne() => mu
		 or x-mu == OneOrMore()	 and One() 			 => mu
		 or x-mu == ZeroOrOne()	 and ZeroOrOne() => mu // --> this should give an error or warning
		 or x-mu == One()				 and One()			 => mu // --> this should give an error or warning
	) 
	else error "Expected multiplicity of higher than One" on x
		
	Concat(x) : x-ty
	where x : x-ty
		and x-ty == String() else error $[Type mismatch: expected String got [x-ty] in Concatenation] on x
		
	Concat(x) has multiplicity One() //TODO: zero goes to multiplicity zero or to empty string?
