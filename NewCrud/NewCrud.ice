module NewCrud

model

  entity Person {
    name : String
    nickname : String?
    fullname : String = name + " " + (nickname <+ "") (default)
    
   	reqInt : Int
   	nonReqInt : Int?
   	reqFloat: Float
   	nonReqFloat : Float?
   	reqBool : Boolean
   	nonReqBool : Boolean?
   	reqDatetime : Datetime
   	nonReqDatetime : Datetime?
  }
  