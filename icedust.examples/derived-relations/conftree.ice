module conftree

model

  entity Conference {
  
  }
  
  relation Conference.parentConf ? <-> Conference.subConf
  
  relation Conference.rootConf ? <-> Conference.descendantConfs // derive this
  
// Option 1: derived value expression
//
// relation Conference.rootConf ? = parent.rootConf <+ parent <-> Conference.descendantConfs
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
