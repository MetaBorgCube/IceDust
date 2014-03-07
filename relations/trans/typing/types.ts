module typing/types

imports
	
  lib/nabl/-
  lib/task/-
  lib/properties/-
  lib/types/-
  lib/editor/-

	include/Relations


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

	Int(x) : Int()
	Int(x) has multiplicity One()
	
	String(x) : String()
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
	
	Multiplication(x, y)
+	Division(x, y)
+	Modulo(x, y)
+	Addition(x, y)
+	Subtraction(x, y) : y-ty
	where	x	: x-ty
		and	y	: y-ty
		and	x-ty == y-ty else error "Not the same types supplied to Addition." on y
		
	Multiplication(x, y)
+	Division(x, y)
+	Modulo(x, y)
+	Addition(x, y)
+	Subtraction(x, y) has multiplicity y-mu
	where	x	has multiplicity x-mu
		and	y	has multiplicity y-mu
		and	x-mu == y-mu else error "Not the same multiplicities supplied to Addition." on y
		
	Aggregation(op, x) : x-ty
		where	x	: x-ty


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
	
		