module objectquery

// model taken from Demand-Driven Incremental Object Queries - PPDP 2016 

model

  entity Celeb {
  
  }
  
  entity User {
    loc   : String
    email : String
  }
  
  relation Celeb.followers * <-> * User.celebs
  
  entity Group {
  
  }
  
  relation User.groups * <-> * Group.members
  
  entity Demand {
    cond   : String    // equality check
    result : String* = users.email
  }
  
  relation Demand.celeb 1 <-> * Celeb.demands
  
  relation Demand.group 1 <-> * Group.demands
  
  relation Demand.users * = group.members.filter(u => u.loc == cond).filter(u => u.celebs.filter(c => c == celeb).count()>0) // schedule: first join group users, then check whether celeb
    <-> * User.demandResults
    
  // comparison with IncOQ
  //
  // update triggers:
  //   User.loc -> groups.demands.users  (which is exactly the first nested for loops in running example in paper - but IceDust re-evalutes full expression instead of modifies cache with deltas)
  //
  // the re-evaluation of the users field triggers:
  //   User.loc -> groups.demands.members.filter(...).filter(u => u.groups.filter(g => g == group))  (which is the remainder of nested for loops. Though IceDust looks at all members of the demand rather than only the changed member. IncOQ only accesses the single changed member.)
  