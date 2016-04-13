module typing/_ordering-functions

imports
	
	// constructors
	src-gen/signatures/Types-sig
	
	// // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/icedust/-

type functions

  or-nav:
    (x-or, y-or) -> or
    where x-or == Ordered() and y-or == Ordered() and Ordered()   => or
       or                                             Unordered() => or

