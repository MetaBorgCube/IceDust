module relationsbetweenrelations // >>> Solving constraints <<< Finished in 18.84s

//model
//
//  entity Person {
//    name : String
//  }
//
//  relation Marriage {
//    Person.marriage  ? -> husband 
//    Person.marriage2 ? -> wife
//    
//    name : String = husband.name + " is married to " + wife.name
//  }
//
//  relation Counseling {
//    Person *   -> counselor
//    Marriage 1 -> counselled
//    
//    name : String = counselor.name + " is counseling " + counselled.husband.name + " and " + counselled.wife.name
//  }
//
//data
//
//  man : Person {
//    name = "Bob"
//    wife =
//      < theMarriage { } >
//      woman {
//        name = "Alice"
//      }
//  }
//  counsellor : Person {
//    name = "Charles"
//    counselled = theMarriage
//  }
//
//execute
//
//  man.marriage.name // get the marriage
//
//  man.marriage.wife.name // get his wife
//
//  man.marriage.counseling.name // go from the man to his marriage to the counseling of this marriage
//
//  man.marriage.counseling.counselor.name // and then get the counselor of this marriage
