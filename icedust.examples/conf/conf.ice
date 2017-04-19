module conf

model
  
  entity Conference {
    name            : String
    rootName        : String = root.name
    numComittees    : Int    = count(comittees)
    numMembers      : Int    = count(comittees.members)
    numMembersTotal : Int    = numMembers + sum(children.numMembersTotal)
  }
  
  relation Conference.parent ? <-> Conference.children

  relation Conference.root 1 = parent.root <+ this
    <-> Conference.rootDescendants

  entity Person {
    name         : String
    numComittees : Int    = count(comittees)
  }
  
  entity Profile {
    name         : String = person.name + " in " + conference.name
    numComittees : Int    = count(comittees)
  }
  
  relation Profile.conference 1 <-> Conference.profiles
  relation Profile.person     1 <-> Person.profiles
  
  entity Committee {
    name       : String
    fullName   : String = conference.name + " " + name
    numMembers : Int    = count(members)
  }
  
  relation Committee.conference 1 <-> Conference.comittees
  relation Committee.members      <-> Person.comittees
  
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
  sle:Conference {
    name = "SLE"
    parent = splash
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
  gttse:Conference {
    name = "GTTSE"
    parent = splash
  }
  
execute

  splashAlice.comittees.fullName // [SPLASH Program Comittee, SPLASH Organizing Comittee]
  
  splashOrganizing.profiles.name // [Bob in SPLASH, Alice in SPLASH] // only works with incremental
  
  splash.numMembersTotal // 7
