module NewCrud

model

  entity Person {
    nickname : String?
    nickname2: String
   	reqInt : Int
   	nonReqInt : Int?
   	reqFloat: Float
   	nonReqFloat : Float?
   	reqBool : Boolean
   	nonReqBool : Boolean?
   	reqDatetime : Datetime
   	nonReqDatetime : Datetime?
   	
   	derived : String = nickname2 + " " + (nickname <+ "")
   	derivedOptional : String? = nickname2 + " " + (nickname <+ "")
   	derivedDefault : String = nickname2 + " " + (nickname <+ "") (default)
   	derivedDefaultOption : String? = nickname2 + " " + (nickname <+ "") (default)
   	
   	derivedInt : Int = reqInt
   	derivedIntOptional : Int? = nonReqInt
   	derivedIntDefault : Int = reqInt (default)
   	derivedIntDefaultOption : Int? = nonReqInt (default)
  }
  