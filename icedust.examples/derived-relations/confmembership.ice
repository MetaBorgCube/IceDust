module confmembership

model

  entity Person {
    name : String
  }
  
  entity Conference {
    name : String
  }
  
  entity Profile {
    name : String = person.name + " in " + conference.name
  }
  
  relation Profile.conference 1 <-> Conference.profiles
  relation Profile.person 1 <-> Person.profiles
  
  entity Committee {
    name     : String
    fullName : String = conference.name + " " + name
  }
  
  relation Committee.conference 1 <-> Conference.comittees
  relation Committee.members <-> Person.comittees
  
  relation Profile.comittees = person.comittees.filter(x => x.conference == this.conference)
    <-> Committee.profiles

data

  alice:Person{
    name = "Alice"
  }
  bob:Person{
    name = "Bob"
  }
  charles:Person{
    name = "Charles"
  }
  
  splash:Conference {
    name = "SPLASH"
    comittees =
      splashOrganizing{
        name = "Organizing Comittee"
        members =
          alice,
          bob
      },
      {
        name = "Program Comittee"
        members =
          alice,
          bob
      }
    profiles =
      splashAlice{
        person = alice
      },
      {
        person = bob
      },
      {
        person = charles
      }
  }
  ecoop:Conference {
    name = "ECOOP"
    comittees =
      {
        name = "Organizing Comittee"
        members =
          charles
      },
      {
        name = "Program Comittee"
        members =
          alice,
          charles
      }
    profiles =
      {
        person = alice
      },
      {
        person = bob
      },
      {
        person = charles
      }
  }
  
execute

  splashAlice.comittees.fullName
  
  splashOrganizing.profiles.name // only works with incremental
