module NewCrud

model

  entity Person {
    name : String
    nickname : String?
    fullname : String = name + " " + (nickname <+ "") (default)
  }
  