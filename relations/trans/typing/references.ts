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

	AttributeName(e, name) : type
	where definition of name : type
	
	// AttributeName(e, name) has multiplicity attr-mu
	// where	definition of name has multiplicity attr-mu
	
	AttributeName(e, name) has multiplicity e-mu
	where	e has multiplicity e-mu
	// 	and definition of name has multiplicity One() else error "Attribute should have multiplicity One" on name

	RoleName(name) : type
	where definition of name : type
	
	Identifier(name) : type
	where definition of name : type
	
	Identifier(name) has multiplicity One() //One() if refers to entity type, One() or ZeroOrOne() if refers to attribute

	This() has multiplicity One()
