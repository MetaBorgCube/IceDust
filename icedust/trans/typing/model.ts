module typing/model

imports

  // constructors
  src-gen/signatures/Data-sig
  src-gen/signatures/Model-sig
  src-gen/signatures/Types-sig   
  trans/api/constructors
  
  // functions
  names/naming/names
  
  // // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

type rules

  Entity(e, [Extends(i)], members):-
    where store e <sub: i
