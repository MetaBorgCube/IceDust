module weblabnext

model

  entity Submission {
  
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
