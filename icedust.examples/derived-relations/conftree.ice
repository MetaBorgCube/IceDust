module conftree

model

  entity Conference {
    name     : String
    rootName : String = rootConf.name
  }
  
  relation Conference.parentConf ? <-> Conference.subConf
  
  //TODO: descendant conf voor alle niet root Confs
  
//  relation Conference.rootConf 1 <-> Conference.descendantConfs // derive this
  
// Option 1: derived value expression

  relation Conference.rootConf 1 = parentConf.rootConf <+ this
    <-> Conference.descendantConfs

// or
//
// relation Conference.descendantConfs <-> ? Conference.rootConf = parent.rootConf <+ parent
//
// or (has probs with ?)
//
// relation Conference.descendantConfs = children ++ children.descendantConfs <-> ? Conference.rootConf
//
// or (has probs with ?)
//
// relation Conference.rootConf ? <-> Conference.descendantConfs = children ++ children.descendantConfs

  relation Conference.allEditions * <-> Conference.dontcare
  
// relation Conference.allEditions * = rootConf.descendantConfs
//           <-> Conference.dontcare
//

data

  splash:Conference{
    name = "SPLASH"
    subConf = 
      sle{
        name = "SLE"
        subConf = 
          subsle{
            name = "subSLE"
          }
      }
  }
  
execute

  sle.name
  sle.parentConf.name
  sle.rootName
  subsle.rootName
