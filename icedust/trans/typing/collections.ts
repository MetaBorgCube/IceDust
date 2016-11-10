module typing/collections

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

  Filter(expr1, x, expr2) : ty1
  where
    expr1 : ty1 and
    expr2 : ty2 and
    ty2 == Boolean() else error $[Type mismatch: expected Boolean got [ty2] in Not] on expr2
  
  Filter(expr1, x, expr2) has multiplicity mu
  where
    expr1 has multiplicity mu1 and
    <lowerbound-zero> (mu1) => mu and
    expr2 has multiplicity mu2 and
    mu2 == One() else error $[Multiplicity mismatch: expected One got [mu2] in Conditional] on expr2
    
  Filter(expr1, x, expr2) has ordering or1
  where
    expr1 has ordering or1

type rules

  First(e):ty
  where
    e:ty
    
  First(e) has multiplicity mu
  where
    e has multiplicity e-mu
    and <upperbound-one> (e-mu) => mu
  
  First(e) has ordering Ordered()
