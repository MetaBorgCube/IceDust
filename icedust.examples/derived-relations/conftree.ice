module conftree

model

  entity Conference {
    name     : String
    rootName : String = rootConf.name
  }
  
  relation Conference.parentConf ? <-> Conference.subConf

  relation Conference.rootConf 1 = parentConf.rootConf <+ this
    <-> Conference.descendantConfs

  relation Conference.allEditions * <-> Conference.dontcare
  
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

  splash.name
  splash.rootName
  sle.name
  sle.rootName
  subsle.name
  subsle.rootName
