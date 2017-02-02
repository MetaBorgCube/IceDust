module typing/_strategy-functions

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

  strategy-least-upperbound:
    (x-st, y-st) -> st
    where x-st == Incremental() and y-st == Incremental()           and Incremental()      => st
       or (x-st == Eventual() or x-st == Incremental())             and
          (y-st == Eventual() or y-st == Incremental())             and Eventual()         => st
       or (x-st ==OnDemandEventual() or y-st == OnDemandEventual()) and OnDemandEventual() => st
       or x-st == OnDemand() and y-st == Eventual()                 and OnDemandEventual() => st
       or y-st == OnDemand() and x-st == Eventual()                 and OnDemandEventual() => st
       or                                                                       OnDemand() => st
