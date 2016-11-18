module weblabnext

model

  entity Submission {
    name : String
  }
  
  relation Submission.parent ? (ordered) <-> * (ordered) Submission.children

  relation Submission.next ? = parent.children.elemAt(parent.children.indexOf(this) + 1)
     <-> ? Submission.previous

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
  