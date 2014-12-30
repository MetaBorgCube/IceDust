module typing/references

imports

	include/Relations
	trans/naming/names

	lib/types/-

type rules // general references

	MemberAccess(expr, member) : member-ty
	where definition of member : member-ty
	
	MemberAccess(expr, member) has multiplicity mu
	where	expr has multiplicity expr-mu
		and definition of member has multiplicity member-mu
		and <cartesian-product> (expr-mu, member-mu) => mu

	Ref(a) : ty
	where definition of a : ty
	
	Ref(a) has multiplicity a-mu
	where definition of a has multiplicity a-mu

	this@This() : ty
	where definition of this : ty 

	This() has multiplicity One()

type rules // specific references

	RoleRef(r) : r-ty
	where definition of r : r-ty
	
	AttributeRef(a) : a-ty
	where definition of a : a-ty
	
	EntityInstanceRef(e) : e-ty
	where definition of e : e-ty
	
	LHSNode(NaBLHelp(v, defuse), t, a)
+ NHSNode(NaBLHelp(v, defuse), t, a)
+	RHSNode(NaBLHelp(v, defuse), t, a) : v-ty
	where definition of v : v-ty

	LHSTsHelp(l, e, e-name) 
+	NHSTsHelp(l, e, e-name) 
+	RHSTsHelp(l, e, e-name) : e-ty
	where definition of e : e-ty

	LHSEdge(e, r)
+	NHSEdge(e, r)
+	RHSEdge(e, r): r-ty
	where r : r-ty

	AttrRef(a) : a-ty
	where definition of a : a-ty

	AttrRef(a) has multiplicity t
	where definition of a has multiplicity t
