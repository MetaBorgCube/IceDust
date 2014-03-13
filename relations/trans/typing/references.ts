module typing/navigators

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations
	trans/naming/names

type rules

	AttributeName(expr, attr) : attr-ty
	where definition of attr : attr-ty
	
	AttributeName(expr, attr) has multiplicity expr-mu
	where	expr has multiplicity expr-mu
	// and definition of attr has attr-mu
	//TODO: use both expr-mu and attr-mu to get result mu

	RoleName(r) : r-ty
	where definition of r : r-ty
	
	Identifier(a) : ty
	where definition of a : ty
	
	Identifier(a) has multiplicity a-mu
	where definition of a has multiplicity a-mu

	//TODO: type of This()

	This() has multiplicity One()
