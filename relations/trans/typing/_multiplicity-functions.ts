module typing/_multiplicity-functions

imports

	include/Relations
	
	lib/types/-

type functions

  cartesian-product:
    (x-mu, y-mu) -> mu
    where x-mu == One() and y-mu == One()               and One()        => mu
       or (x-mu == ZeroOrOne() or x-mu == One())        and
          (y-mu == ZeroOrOne() or y-mu == One())        and ZeroOrOne()  => mu
       or (x-mu ==ZeroOrMore() or y-mu == ZeroOrMore()) and ZeroOrMore() => mu
       or x-mu == OneOrMore() and y-mu == ZeroOrOne()   and ZeroOrMore() => mu
       or y-mu == OneOrMore() and x-mu == ZeroOrOne()   and ZeroOrMore() => mu
       or                                                   OneOrMore()  => mu

  lowerbound-zero:
  	(x-mu) -> mu
  	where (x-mu == ZeroOrOne() or x-mu == One()) and ZeroOrOne()  => mu
  	   or                                            ZeroOrMore() => mu

  upperbound-one:
    (x-mu) -> mu
    where (x-mu == OneOrMore() or x-mu == One()) and One()       => mu
       or                                            ZeroOrOne() => mu

  mu-choice:
    (x-mu, y-mu) -> mu
    where x-mu == One()                                 and One()        => mu
       or x-mu == OneOrMore()                           and OneOrMore()  => mu
       or x-mu == ZeroOrOne() and y-mu == ZeroOrOne()   and ZeroOrOne()  => mu
       or (x-mu == ZeroOrOne() or x-mu == ZeroOrMore()) and
          (y-mu == ZeroOrOne() or y-mu == ZeroOrMore()) and ZeroOrMore() => mu
       or x-mu == ZeroOrOne() and y-mu == One()         and One()        => mu
       or                                                   OneOrMore()  => mu

  mu-merge:
    (x-mu, y-mu) -> mu
    where (x-mu == One() or x-mu == OneOrMore() or
           y-mu == One() or y-mu == OneOrMore())    and OneOrMore()  => mu
       or                                               ZeroOrMore() => mu
