module conftree

model

  entity Conference {
  
  }
  
  relation Conference.parentConf ? <-> Conference.subConf
  
  //TODO: descendant conf voor alle niet root Confs
  
  relation Conference.rootConf 1 <-> Conference.descendantConfs // derive this
  
// Option 1: derived value expression
//
// @cached
// relation Conference.rootConf 1 = parent.rootConf <+ this
// <-> Conference.descendantConfs
//
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
