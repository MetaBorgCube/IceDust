module objectquery2

// model taken from Generating Incremental Implementations of Object-Set Queries - GPCE 2008

model
  
  entity User {
    id : String
  }
  
  entity Group {
    active : Boolean
  }
  
  relation User.groups * <-> * Group.members
  
  entity Permission {
    name : String
  }
  
  relation Group.perms * <-> * Permission.groups
  
  entity Query {
    uid    : String
    result : String* = permissions.name
  }
  
  relation Query.users * <-> * User.queries
  
  relation Query.user ? = users.find(u => u.id == uid)
    <-> User.queries2 // cache the user per query
  
  relation Query.permissions * = user.groups.filter(g => g.active).perms
    <-> Permission.queries
   
  // comparison with Object-Set Queries
  //
  // update triggers:
  //   User.groups -> queries2.permissions  (triggers reevaluation for all queries of which this user is of interest)
  //
  // the re-evaluation of the permissions field triggers:
  //   User.groups -> queries2.user.groups.filter(g => g.active).perms  (reads all groups of the query, rather than only the single group that is added, OSQ uses deltas, IceDust does not)
  //
  // the order of forloops in OSQ is different:
  //   - group.permissions                    (this IceDust implementation selects permissions of all relevent queries.user.groups at the end)
  //       group.users.filter(_.id == uid)    (this IceDust implementation filters users second)
  //       group.users is in a query          (this IceDust implementation filter on queries first)
  