module types

imports



type rules

	
	//FIXME: attribute value assignment doesn't appear to trigger errors yet.
	AttributeValue(attributeName, attributeValue) :-
		where	attributeName	: attributeType
		and		attributeValue	: valueType
		and		attributeType == valueType 
		else error "Wrong type supplied" on attributeValue
