module typing/literals

imports

	// constructors
	src-gen/signatures/Expressions-sig
	src-gen/signatures/Types-sig
	
	// functions
  names/naming/names
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

type rules

	Int(x) : Int()
	Int(x) has multiplicity One()
	Int(x) has ordering Ordered()

	Float(x) : Float()
	Float(x) has multiplicity One()
	Float(x) has ordering Ordered()
	
	String(x) : String()
	String(x) has multiplicity One()
	String(x) has ordering Ordered()
	
	True() : Boolean()
	True() has multiplicity One()
	True() has ordering Ordered()
	
	False() : Boolean()
	False() has multiplicity One()
	False() has ordering Ordered()
	
	Datetime(x) : Datetime()
	Datetime(x) has multiplicity One()
	Datetime(x) has ordering Ordered()
	
	NoValue() : NoValue()
	NoValue() has multiplicity ZeroOrOne()
	NoValue() has ordering Ordered()
