module JSTest

model

  entity Person {
    name : String
    summary : String = name + " has a pet called " + pet.name
  }
  
  entity Animal {
    name : String
  }
  
  relation Person.pet 1 <-> 1 Animal.owner
  
data

  albert : Person {
    name = "Albert"
    pet = {
      name = "Miro"
    }
  }
  