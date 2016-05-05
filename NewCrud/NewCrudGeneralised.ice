module NewCrud

model

  entity Entity {
    name : String
    nickname : String?
    fullname : String = name + " " + (nickname <+ "") (default)
  }
  