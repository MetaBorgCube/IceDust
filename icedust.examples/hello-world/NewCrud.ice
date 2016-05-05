module NewCrud

model

  entity Person {
    nickname : String?
    
   	reqInt : Int
   	nonReqInt : Int?
   	reqFloat: Float
   	nonReqFloat : Float?
   	reqBool : Boolean
   	nonReqBool : Boolean?
   	reqDatetime : Datetime
   	nonReqDatetime : Datetime?
  }
  