module ternary // >>> Solving constraints <<< Finished in 14.12s

//model
//
//  entity Supplier {
//    name : String
//  }
//
//  entity Part {
//    name : String
//    nameMany : String  = name + "s" (default) // not all names are +s for multiple
//  }
//
//  entity Project {
//    name : String
//  }
//
//  relation Supply {
//    Supplier * 
//    Part * 
//    Project * 
//    amount : Int  
//    
//    name : String = supplier.name + " supplies " + amount as String + " " + part.nameMany + " to " + project.name
//  }
//
//data
//
//  s : Supplier {
//    name = "MySupplier"
//  }
//  
//  p : Part {
//    name = "SomePart"
//  }
//  
//  pr : Project {
//    name = "AwesomeProject"
//  }
//  
//  x : Supply {
//    supplier = s
//    part = p
//    project = pr
//    amount = 10
//  }
//  
//  y : Supply {
//    supplier = s
//    part = p
//    project = pr
//    amount = 42
//  }
//
//execute
//
//  p.supply.name // this part participates in two supply relations
//
//  p.supply.amount // and these two have both an amount
//
//  p.supply.supplier.name // this part is supplied two times, but both by the same supplier -> 1 supplier, set based navigation
//
//  p.supply.project.name // and to the same project -> 2 x project, bag based navigation
