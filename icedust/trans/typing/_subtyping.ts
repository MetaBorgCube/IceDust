module typing/_subtyping

imports

  // constructors
  src-gen/signatures/Expressions-sig
  src-gen/signatures/Types-sig
  
  // functions
   names/naming/names

relations

  define transitive <sub: 

  NoValue() <sub: Int()
  NoValue() <sub: Float()
  NoValue() <sub: String()
  NoValue() <sub: Boolean()
  NoValue() <sub: Datetime()
    
type functions

  least-upper-bound: False() -> False() // implemented manually
