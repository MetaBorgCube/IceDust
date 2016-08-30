module typing/aggregation

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
 //  lib/relations/-

type rules

  Min(x)
+ Max(x)
+ Sum(x)
+ Avg(x) : x-ty
  where  x  : x-ty
    and (x-ty == Int() or x-ty == Float() or x-ty == NoValue())
        else error $[Type mismatch: expected Int got [x-ty] in Aggregation] on x

  Conj(x)
+ Disj(x) : x-ty
  where  x  : x-ty
    and (x-ty == Boolean() or x-ty == NoValue()) 
        else error $[Type mismatch: expected Boolean got [x-ty] in Aggregation] on x

  Concat(x) : x-ty
  where x : x-ty
    and x-ty == String() else error $[Type mismatch: expected String got [x-ty] in Concatenation] on x

  Count(x) : Int()

  Min(x)
+ Max(x)
+ Avg(x) has multiplicity mu
  where x has multiplicity x-mu
    and <upperbound-one> (x-mu) => mu
    and (x-mu == ZeroOrMore() or x-mu == OneOrMore())  else error "Expected multiplicity of higher than One" on x //should be a warning, not an error

  Conj(x)
+ Disj(x)
+ Concat(x)
+ Sum(x) has multiplicity One()
  where x has multiplicity x-mu
    and (x-mu == ZeroOrMore() or x-mu == OneOrMore())  else error "Expected multiplicity of higher than One" on x //should be a warning, not an error
  
  Count(x) has multiplicity One()

  Min(x)
+ Max(x)
+ Avg(x)
+ Conj(x)
+ Disj(x)
+ Concat(x)
+ Sum(x)
+ Count(x) has ordering Ordered()
