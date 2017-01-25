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
  
  Float(x) : Float()
  Float(x) has multiplicity One()
  
  LitString(x) : String()
  LitString(x) has multiplicity One()
  
  True() : Boolean()
  True() has multiplicity One()
  
  False() : Boolean()
  False() has multiplicity One()
  
  Datetime(x) : Datetime()
  Datetime(x) has multiplicity One()
  
  NoValue() : NoValue()
  NoValue() has multiplicity ZeroOrOne()

  Int(x)
+ Float(x)
+ LitString(x)
+ True()
+ False() 
+ Datetime(x)
+ NoValue() has strategy Incremental() //bottom of lattice
  