module typing/aggregation

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations


type rules

	Int(x) : Int()
	Int(x) has multiplicity One()
	
	String(x) : String()
	String(x) has multiplicity One()
	
	True() : Boolean()
	True() has multiplicity One()
	
	False() : Boolean()
	False() has multiplicity One()