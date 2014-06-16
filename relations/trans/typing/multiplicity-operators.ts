module typing/multiplicity-operators

imports

	include/Relations

type rules

	ChoiceLeft(x,y) : x-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Choice] on y
		
	ChoiceLeft(x,y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and <mu-choice> (x-mu, y-mu) => mu
		
	Merge(x,y) : x-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error $[Type mismatch: expected [x-ty] got [y-ty] in Merge] on y
		
	Merge(x,y) has multiplicity mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity  y-mu
		and <mu-merge> (x-mu, y-mu) => mu
		
type functions

  mu-choice:
    (x-mu, y-mu) -> mu
    where x-mu == One()                                 and One()        => mu
       or x-mu == OneOrMore()                           and OneOrMore()  => mu
       or x-mu == ZeroOrOne() and y-mu == ZeroOrOne()   and ZeroOrOne()  => mu
       or (x-mu == ZeroOrOne() or x-mu == ZeroOrMore()) and
          (y-mu == ZeroOrOne() or y-mu == ZeroOrMore()) and ZeroOrMore() => mu
       or x-mu == ZeroOrOne() and y-mu == One()         and One()        => mu
       or                                                   OneOrMore()  => mu


	// if one of the multiplicities have a lower bound of One then OneOrMore else ZeroOrMore
  mu-merge:
    (x-mu, y-mu) -> mu
    where (x-mu == One() or x-mu == OneOrMore() or
           y-mu == One() or y-mu == OneOrMore())    and OneOrMore()  => mu
       or                                               ZeroOrMore() => mu
