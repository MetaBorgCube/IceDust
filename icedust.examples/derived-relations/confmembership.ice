module confmembership

model

  entity Person {
  
  }
  
  entity Conf {
  
  }
  
  entity Profile {
  
  }
  
  relation Profile.conf 1 <-> Conf.profiles
  relation Profile.person 1 <-> Person.profiles
  
  entity Group {
  
  }
  
  relation Group.conf <-> Conf.groups
  relation Group.members <-> Person.groups
  
  relation Profile.groups <-> Group.profiles // derive this
  
// Option 1: derived value expression
//
// relation Profile.groups <-> Group.profiles = members.profiles.filter(x => x.conf == conf)

// Option 2: datalog-style (with .notation)
//
// relation p:Profile.groups <-> g:Group.profiles {
//   p = g.members.profiles
//   p = g.conf.profiles
// } 

// Option 3: datalog-style (with .notation) restricted
//
// relation Profile.groups <-> Group.profiles {
//   members.profiles
//   conf.profiles
// }
