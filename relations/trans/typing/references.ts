module typing/navigators

imports

	include/Relations
	trans/naming/names

type rules

	MemberAccess(expr, member) : member-ty
	where definition of member : member-ty
	
	MemberAccess(expr, member) has multiplicity mu
	where	expr has multiplicity expr-mu
		and definition of member has multiplicity member-mu
		and <mu-or-join> (expr-mu, member-mu) => mu

	RoleName(r) : r-ty
	where definition of r : r-ty
	
	Identifier(a) : ty
	where definition of a : ty
	
	Identifier(a) has multiplicity a-mu
	where definition of a has multiplicity a-mu

	this@This() : ty
	where definition of this : ty 

	This() has multiplicity One()


type functions

	mu-or-join:
		(x-mu, y-mu) -> mu
		where x-mu == One() and y-mu == One()																										and One() => mu
			 or (x-mu == ZeroOrOne() or x-mu == One()) and (y-mu == ZeroOrOne() or y-mu == One()) and ZeroOrOne() => mu
			 or (x-mu == ZeroOrMore() or y-mu == ZeroOrMore())																		and ZeroOrMore() => mu
			 or x-mu == OneOrMore() and y-mu == ZeroOrOne()																				and ZeroOrMore() => mu
			 or y-mu == OneOrMore() and x-mu == ZeroOrOne()																				and ZeroOrMore() => mu
			 or																																												OneOrMore() => mu

