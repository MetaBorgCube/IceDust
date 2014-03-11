module typing/math

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

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
+	Subtraction(x, y) has multiplicity y-mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and	x-mu == y-mu else error $[Multiplicity mismatch: expected [x-mu] got [y-mu] in Math Operation] on y