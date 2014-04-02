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
		where (x-mu == One() 			 and One() => mu)										//[1,1]<+_																										: [1,1]
			 or (x-mu == OneOrMore() and OneOrMore() => mu)							//[1,n)<+_																										: [1,n)
			 or (x-mu == ZeroOrOne() and y-mu == ZeroOrOne() and ZeroOrOne() => mu) //[0,1]<+[0,1]																		: [0,1]
			 or (																												//[0,1]<+[0,n), [0,n)<+[0,1] and [0,n)<+[0,n)									: [0,n)
			 				(x-mu == ZeroOrOne() or x-mu == ZeroOrMore())
			 		and (y-mu == ZeroOrOne() or y-mu == ZeroOrMore())
			 		and ZeroOrMore() => mu
			 		)
			 or (x-mu == ZeroOrOne() and y-mu == One() and One() => mu)	//[0,1]<+[1,1]																								: [1,1]
			 or OneOrMore() => mu																				//[0,1]<+[1,n), [0,n)<+[1,1] and [0,n)<+[1,n)									: [1,n)


	// if one of the multiplicities have a lower bound of One then OneOrMore else ZeroOrMore
	mu-merge:
		(x-mu, y-mu) -> mu
		where (																												//[1,1]::_, [1,n)::_, _::[1,1] and _::[1,n)										: [1,n)
					(x-mu == One() or x-mu == OneOrMore() or y-mu == One() or y-mu == OneOrMore())
					and OneOrMore() => mu
					)
			 or ZeroOrMore() => mu																			//rest																												: [0,n)
