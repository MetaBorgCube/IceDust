module typing/_multiplicity-functions

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

  cartesian-product: (x-mu, y-mu) -> mu
    where x-mu == One()                                              and y-mu                => mu // [1,1] -> identity
       or y-mu == One()                                              and x-mu                => mu // [1,1] -> identity
       or x-mu == ZeroOrMore()                                       and ZeroOrMore()        => mu // [0,n) unordered -> top of lattice
       or y-mu == ZeroOrMore()                                       and ZeroOrMore()        => mu // [0,n) unordered -> top of lattice
       or x-mu == ZeroOrOne()        and y-mu == ZeroOrOne()         and ZeroOrOne()         => mu // diagonal -> identity
       or x-mu == OneOrMoreOrdered() and y-mu == OneOrMoreOrdered()  and OneOrMoreOrdered()  => mu // diagonal -> identity
       or y-mu == OneOrMore()        and x-mu == OneOrMore()         and OneOrMore()         => mu // diagonal -> identity
       or x-mu == OneOrMore()        and y-mu == ZeroOrOne()         and ZeroOrMore()        => mu // [1,n) unordered -> upper-bound many, drop ordering
       or y-mu == OneOrMore()        and x-mu == ZeroOrOne()         and ZeroOrMore()        => mu // [1,n) unordered -> upper-bound many, drop ordering
       or x-mu == OneOrMore()        and y-mu == ZeroOrMoreOrdered() and ZeroOrMore()        => mu // [1,n) unordered -> upper-bound many, drop ordering
       or y-mu == OneOrMore()        and x-mu == ZeroOrMoreOrdered() and ZeroOrMore()        => mu // [1,n) unordered -> upper-bound many, drop ordering
       or x-mu == OneOrMore()        and y-mu == OneOrMoreOrdered()  and OneOrMore()         => mu // [1,n) unordered -> upper-bound many, drop ordering
       or y-mu == OneOrMore()        and x-mu == OneOrMoreOrdered()  and OneOrMore()         => mu // [1,n) unordered -> upper-bound many, drop ordering
       or                                                                ZeroOrMoreOrdered() => mu // rest -> [0,n) ordered

  lowerbound-zero: (x-mu) -> mu
    where (x-mu == ZeroOrOne()         or x-mu == One()             ) and ZeroOrOne()         => mu
       or (x-mu == ZeroOrMore()        or x-mu == OneOrMore()       ) and ZeroOrMore()        => mu
       or (x-mu == ZeroOrMoreOrdered() or x-mu == OneOrMoreOrdered()) and ZeroOrMoreOrdered() => mu

  upperbound-one: (x-mu) -> mu
    where (x-mu == One() or x-mu == OneOrMore() or x-mu == OneOrMoreOrdered()) and One()       => mu
       or                                                                          ZeroOrOne() => mu

  mu-choice: (x-mu, y-mu) -> mu
    where x-mu == One()                                               and x-mu                => mu // [1,_] -> always left-hand side operand
       or x-mu == OneOrMore()                                         and x-mu                => mu // [1,_] -> always left-hand side operand
       or x-mu == OneOrMoreOrdered()                                  and x-mu                => mu // [1,_] -> always left-hand side operand
       or x-mu == ZeroOrOne()                                         and y-mu                => mu // [0,1] -> always right-hand side multiplicity
       or y-mu == ZeroOrMore()                                        and y-mu                => mu // [0,_] <+ [0,n) unordered -> always [0,n) unordered
       or y-mu == OneOrMore()                                         and y-mu                => mu // [0,_] <+ [1,n) unordered -> always [1,n) unordered
       or x-mu == ZeroOrMoreOrdered() and y-mu == ZeroOrOne()         and ZeroOrMoreOrdered() => mu // [0,n) ordered -> upper-bound many
       or x-mu == ZeroOrMoreOrdered() and y-mu == One()               and OneOrMoreOrdered()  => mu // [0,n) ordered -> upper-bound many
       or x-mu == ZeroOrMoreOrdered() and y-mu == ZeroOrMoreOrdered() and ZeroOrMoreOrdered() => mu // [0,n) ordered -> upper-bound many
       or x-mu == ZeroOrMoreOrdered() and y-mu == OneOrMoreOrdered()  and OneOrMoreOrdered()  => mu // [0,n) ordered -> upper-bound many
       or x-mu == ZeroOrMore()        and y-mu == ZeroOrOne()         and ZeroOrMore()        => mu // [0,n) unordered -> upper-bound many, drop ordering
       or x-mu == ZeroOrMore()        and y-mu == One()               and OneOrMore()         => mu // [0,n) unordered -> upper-bound many, drop ordering
       or x-mu == ZeroOrMore()        and y-mu == ZeroOrMoreOrdered() and ZeroOrMore()        => mu // [0,n) unordered -> upper-bound many, drop ordering
       or x-mu == ZeroOrMore()        and y-mu == OneOrMoreOrdered()  and OneOrMore()         => mu // [0,n) unordered -> upper-bound many, drop ordering

  mu-merge: (x-mu, y-mu) -> mu
    where x-mu == OneOrMore()                                         and OneOrMore()         => mu // [1,_] unordered -> [1,n) unordered
       or y-mu == OneOrMore()                                         and OneOrMore()         => mu // [1,_] unordered -> [1,n) unordered
       or x-mu == ZeroOrMore()        and y-mu == One()               and OneOrMore()         => mu // [0,n) unordered ++ [1,_] -> [1,n) unordered
       or y-mu == ZeroOrMore()        and x-mu == One()               and OneOrMore()         => mu // [0,n) unordered ++ [1,_] -> [1,n) unordered
       or x-mu == ZeroOrMore()        and y-mu == OneOrMoreOrdered()  and OneOrMore()         => mu // [0,n) unordered ++ [1,_] -> [1,n) unordered
       or y-mu == ZeroOrMore()        and x-mu == OneOrMoreOrdered()  and OneOrMore()         => mu // [0,n) unordered ++ [1,_] -> [1,n) unordered
       or x-mu == ZeroOrMore()                                        and ZeroOrMore()        => mu // [0,n) unordered remaining -> [0,n) unordered
       or y-mu == ZeroOrMore()                                        and ZeroOrMore()        => mu // [0,n) unordered remaining -> [0,n) unordered
       or x-mu == ZeroOrOne()         and y-mu == ZeroOrOne()         and ZeroOrMoreOrdered() => mu // [0,_] ordered ++ [0,_] ordered -> [0,n) ordered
       or x-mu == ZeroOrOne()         and y-mu == ZeroOrMoreOrdered() and ZeroOrMoreOrdered() => mu // [0,_] ordered ++ [0,_] ordered -> [0,n) ordered
       or x-mu == ZeroOrMoreOrdered() and y-mu == ZeroOrOne()         and ZeroOrMoreOrdered() => mu // [0,_] ordered ++ [0,_] ordered -> [0,n) ordered
       or x-mu == ZeroOrMoreOrdered() and y-mu == ZeroOrMoreOrdered() and ZeroOrMoreOrdered() => mu // [0,_] ordered ++ [0,_] ordered -> [0,n) ordered
       or                                                                 OneOrMoreOrdered()  => mu // rest -> [1,n) ordered
