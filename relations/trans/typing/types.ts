module typing/types

imports

	include/Relations
	trans/desugaring/constructors


type rules // type inference : model
		
	AttributeName(e, name) : type
	where definition of name : type
		
	RoleName(name) : type
	where definition of name : type
	
	EntityName(name) : type
	where definition of name : type


type rules // type inference : expressions

	Integer(x) : PrimitiveType("Int")
	String(x) : PrimitiveType("String")
	

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


type rules // constraints: navigators

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
		