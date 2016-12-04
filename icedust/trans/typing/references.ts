module typing/references

imports

  // constructors
  src-gen/signatures/Data-sig
  src-gen/signatures/Expressions-sig
  src-gen/signatures/Model-sig
  src-gen/signatures/Types-sig
  trans/api/constructors
  trans/desugaring/constructors
  
  // functions
  typing/_multiplicity-functions
  typing/_ordering-functions
  names/naming/names
  
  // // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

type rules // general references

  MemberAccess(expr, member) : member-ty
  where definition of member : member-ty
  
  MemberAccess(expr, member) has multiplicity mu
  where  expr has multiplicity expr-mu
    and definition of member has multiplicity member-mu
    and <cartesian-product> (expr-mu, member-mu) => mu
  
  MemberAccess(expr, member) has ordering or
  where  expr has ordering expr-or
    and definition of member has ordering member-or
    and <or-nav> (expr-or, member-or) => or
  
  MemberAccess(expr, member) has strategy st
  where  expr has strategy expr-st
    and definition of member has strategy member-st
    and <strategy-least-upperbound> (expr-st, member-st) => st

  Ref(a) : ty
  where definition of a : ty
  
  Ref(a) has multiplicity a-mu
  where definition of a has multiplicity a-mu
  
  Ref(a) has ordering a-or
  where definition of a has ordering a-or

  Ref(a) has strategy st
  where definition of a has strategy st

  this@This() : ty
  where definition of this : ty 

  This() has multiplicity One()

  This() has ordering Ordered()

  This() has strategy Incremental()

type rules // specific references

  RoleRef(r) : r-ty
  where definition of r : r-ty
  
  AttributeRef(a) : a-ty
  where definition of a : a-ty
  
  MemberRef(m) : m-ty
  where definition of m : m-ty
  
  MemberRef(m) has multiplicity m-mu
  where definition of m has multiplicity m-mu
  
  MemberRef(m) has ordering m-or
  where definition of m has ordering m-or
  
  MemberRef(m) has rel-ty r-ty
  where definition of m has rel-ty r-ty
  
  EntityInstanceRef(e) : e-ty
  where definition of e : e-ty
  
  EntityInstanceRef(e) has multiplicity One()
  
  EntityInstanceRef(e) has ordering Ordered()
  
  EntityRef(e) : e-ty
  where definition of e => e-ty
  
  EntityRef(e) has multiplicity One()
  
  EntityRef(e) has ordering Ordered()

