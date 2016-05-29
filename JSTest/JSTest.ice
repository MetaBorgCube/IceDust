module JSTest

model

  entity Person {
    personName : String
   	boolean : Boolean
   	booleanOptional : Boolean?
   	derived : String = "You are " + personName
   	derivedDefault : String = "You are " + personName (default)
  }
  