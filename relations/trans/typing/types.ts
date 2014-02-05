module typing/types

imports

	include/Relations
	trans/desugaring/desugar

type rules // constraints

	//attribute assignment
	AttributeValue(attributeName, attributeValue) :-
		where	attributeName		: attributeType					//FIXME: (#1) doesn't work without the rule in types.str
		and		attributeValue	: valueType
		and		attributeType == valueType
		else error "Wrong type supplied" on attributeValue		//TODO: give expected and given type
		
	//role assignment
	RoleValue(roleName, valueEntityName) :-
		where	roleName				: roleType						//FIXME: (#1)
		and		valueEntityName	: valueType						//FIXME: (#1)
		and		roleType == valueType
		else error "Wrong type supplied" on valueEntityName		//TODO: give expected and given type
		
	//default and derived attributes
	Attribute(name, type, Derivation(expression, derivationType)) :-
		where	expression		: expressionType
		and		expressionType == type
		else error "Wrong type supplied" on expression

type rules // expressions
	BinExp(operator, exp1, exp2) : exp2type
		where	exp1		: exp1type
		and		exp2		: exp2type
		and		exp1type == exp2type
		else error "Not the same types supplied to the Binary Operator." on exp2
		