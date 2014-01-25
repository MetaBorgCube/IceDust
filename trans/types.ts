module types

imports



type rules

	//attribute assignment
	AttributeValue(attributeName, attributeValue) :-
		where	attributeName	: attributeType					//FIXME: (#1) doesn't work without the rule in types.str
		and		attributeValue	: valueType
		and		attributeType == valueType
		else error "Wrong type supplied" on attributeValue
		
	//role assignment
	RoleValue(roleName, valueEntityName) :-
		where	roleName		: roleType						//FIXME: (#1)
		and		valueEntityName	: valueType						//FIXME: (#1)
		and		roleType == valueType
		else error "Wrong type supplied" on valueEntityName
