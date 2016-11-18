module weblabnext

model

  entity Submission {
    name : String
  }
  
  relation Submission.parent ? (ordered) <-> * (ordered) Submission.children
  
//  relation Submission.next ? <-> ? Submission.previous // derive this

// Option 1: derived value expression
//  - issue with ? on previous

  relation Submission.next ? = parent.children.elemAt(parent.children.indexOf(this) + 1)
     <-> ? Submission.previous

// Option 2: derived value expression twosided
//  - don't know whether these expressions are the inverse of each other
//
// relation Submission.next ? = parent.children[ parent.children.indexOf(this) + 1 ]
//  <-> Submission.previous ? = parent.children[ parent.children.indexOf(this) - 1 ]

// Option 3: some predefined things for ordered relations
//
// Submission.next = next(parent)
// Submission.previous = previous(parent)

data

  parentSub:Submission {
    name = "parentSub"
    children =
      child1{name="child1"},
      child2{name="child2"},
      child3{name="child3"}
  }
  
execute

  child1.previous.name //previous only works with incremental
  child1.next.name
  child2.previous.name //previous only works with incremental
  child2.next.name
  child3.previous.name //previous only works with incremental
  child3.next.name
  