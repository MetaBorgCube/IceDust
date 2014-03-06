module typing/types

imports

	include/Relations
	trans/desugaring/constructors


type rules // type inference : model
		
	AttributeName(e, name) : type
	where definition of name : type
	AttributeName(e, name) has multiplicity mult
	where definition of name has multiplicity mult
		
	RoleName(name) : type
	where definition of name : type
	
	EntityName(name) : type
	where definition of name : type


type rules // type inference : expressions

	Integer(x) : PrimitiveType("Int")
	Integer(x) has multiplicity One()
	
	String(x) : PrimitiveType("String")
	String(x) has multiplicity One()
	
	Attribute(a, t, e) has multiplicity One()
	

type rules // constraints: attributes & values

	//attribute assignment
	AttributeValue(attributeName, attributeValue) :-
		where	attributeName		: attributeType
		and		attributeValue	: valueType
		and		attributeType == valueType
		else error "Wrong type supplied" on attributeValue		//TODO: give expected and given type

	//role assignment
	RoleValue(roleName, valueEntityName) :-
		where	roleName				: roleType
		and		valueEntityName	: valueType
		and		roleType == valueType
		else error "Wrong type supplied" on valueEntityName		//TODO: give expected and given type

	//default and derived attributes
	Attribute(name, type, Derivation(expression, derivationType)) :-
		where	expression		: expressionType
		and		expressionType == type
		else error "Wrong type supplied" on expression


type rules // constraints: expressions
	
	BinExp(exp1, operator, exp2) : exp2type
		where	exp1		: exp1type
		and		exp2		: exp2type
		and		exp1type == exp2type
		else error "Not the same types supplied to the Binary Operator." on exp2
	BinExp(exp1, operator, exp2) has multiplicity exp2mult
		where	exp1		has multiplicity exp1mult
		and		exp2		has multiplicity exp2mult
		and		exp1mult == exp2mult
		else error "Not the same multiplicities supplied to the Binary Operator." on exp2
		
	Aggregation(operator, exp) : expType
		where	exp			: expType


type rules // constraints: navigators

	//TODO: remove this rule after this is name bound and type checked - This() is not type checked
	NavigateIn(This(), navType, inRole, EntityType(relationType)) : relationType
		where inRole		: inRoleType
	NavigateOut(This(), navType, EntityType(relationType), outRole) : outType
		where	outRole	: outType

	NavigateIn(prevNav, navType, inRole, EntityType(relationType)) : relationType
		where prevNav	: prevNavType
		and inRole		: inRoleType
		and prevNavType == inRoleType
		else error "The inRole is of the wrong type." on inRole
	
	NavigateOut(prevNav, navType, EntityType(relationType), outRole) : outType
		where	outRole	: outType
		and prevNav		: prevNavType
		and relationType == prevNavType
		else error "The relation is of the wrong type." on relationType
	
		