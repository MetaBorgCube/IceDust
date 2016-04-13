module typing/casts

imports

	// constructors
	src-gen/signatures/Expressions-sig
	src-gen/signatures/Types-sig
	trans/api/constructors
	trans/desugaring/constructors
	
	// functions
	typing/_multiplicity-functions
  names/naming/names
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/icedust/-

type rules // derivations well-formedness

	Cast(e, Int()) : Int()
	where e : e-ty
	  and (e-ty == Float() or e-ty == NoValue()) else error $[Type mismatch: expected Float got [e-ty] in Cast to Int] on e
	  
	Cast(e, Float()) : Float()
	where e : e-ty
	  and (e-ty == Int() or e-ty == NoValue()) else error $[Type mismatch: expected Int got [e-ty] in Cast to Float] on e
	  
	Cast(e, String()) : String()
	where e : e-ty
	  and not e-ty == String() else error $[Type mismatch: expected not String got [e-ty] in Cast to String] on e
	  
	x@Cast(e, Boolean()) : Boolean()
	where e : e-ty
	  and e-ty == NoValue() else error $[Cast to Boolean not supported] on x	 
	   
	x@Cast(e, Datetime()) : Datetime()
	where e : e-ty
	  and e-ty == NoValue() else error $[Cast to Datetime not supported] on x

	Cast(e, cast-ty) has multiplicity e-mu
	where e has multiplicity e-mu
	
	Cast(e, cast-ty) has ordering e-or
	where e has ordering e-or
