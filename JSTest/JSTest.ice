module JSTest

model

  entity Person {
    personName : String
   	
   	derived : String = "You are " + personName
  }
  