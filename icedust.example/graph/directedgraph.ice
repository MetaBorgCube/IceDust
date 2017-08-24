module directedgraph // >>> Solving constraints <<< Finished in 6.41s

//model
//
//  entity Node {
//    name : String  
//  }
//  
//  relation Node.from <-> Node.to //{} //TODO: get NaBL2 desugaring bug fixed
//  
//data
//
//  // cyclic graph: a -> b -> c -> a
//
//  a : Node {
//    name = "a"
//    to = b {
//      name = "b"
//      to = c {
//        name = "c"
//        to = a
//      }
//    }
//  }
//
//execute
//
//  a.name
//  b.name
//  c.name
//  a.to.name //must be [b]
//  a.from.name //must be [c]
//  a.to.to.name //must be [c]
//  a.to.to.to.name //must be [a]
