module typing/multiplicity-operators

imports

	// constructors
	src-gen/signatures/Expressions-sig
	src-gen/signatures/Types-sig
	
	// functions
	typing/_multiplicity-functions
  names/naming/names
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/icedust/-

type rules

	ChoiceLeft(x,y) : x-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Choice] on y
		
	ChoiceLeft(x,y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and <mu-choice> (x-mu, y-mu) => mu
		
  Comma(x,y)
+ Merge(x,y) : x-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Merge] on y
		
  Comma(x,y)
+ Merge(x,y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity  y-mu
		and <mu-merge> (x-mu, y-mu) => mu

	ChoiceLeft(x,y)
+	Merge(x,y) has ordering or
	where	x	has ordering x-or
		and	y	has ordering  y-or
		and <or-nav> (x-or, y-or) => or
