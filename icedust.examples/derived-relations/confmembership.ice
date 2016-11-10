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
  
  entity Committee {
  
  }
  
  relation Committee.conf <-> Conf.memberships
  relation Committee.members <-> Person.memberships
  
  relation Profile.memberships <-> Committee.profiles // derive this
  
// Option 1: derived value expression
//
// relation Profile.memberships <-> Committee.profiles = members.profiles.filter(x => x.conf == this.conf)
//
// or
//
// relation Profile.memberships = person.memberships.filter(x => x.conf == this.conf)
//  <-> Committee.profiles

// Option 2: datalog-style (with .notation)
//
// relation p:Profile.memberships <-> g:Committee.profiles {
//   p = g.members.profiles
//   p = g.conf.profiles
// } 

// Option 3: datalog-style (with .notation) restricted
//
// relation Profile.memberships <-> Committee.profiles {
//   members.profiles
//   conf.profiles
// }
