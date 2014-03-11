module typing/choice

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations

type rules

	ChoiceLeft(x,y) : x-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Choice] on y
		
	ChoiceLeft(x,y) has multiplicity One()	//TODO: both the min and max should me upped to the maximum of the options
	where	x	: x-mu
		and	y	: y-mu
		
	Merge(x,y) : x-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Merge] on y
		
	Merge(x,y) has multiplicity OneOrMore()	//TODO: both the min and max should me upped to the maximum of the options
	where	x	: x-mu
		and	y	: y-mu