module weblabsubmissions

model

  entity Assignment {
    name : String
  }

  entity Submission {
    name : String
  }

  entity Student {
    name : String
  }

  relation Assignment.submissions <-> 1 Submission.assignment

  relation Assignment.parent ? <-> Assignment.children

  relation Student.submissions <-> 1 Submission.student

//  relation Submission.parent ? <-> Submission.children // TODO: derive this

// Option 1: derived value expression
//  - uses .first() hack to get multiplicity down from * to ?
//  - other side of relation must be * multiplicity, unless specifying another expression for that
//  + allows arbitrary expressions

  relation Submission.parent ? = assignment.parent.submissions.filter(x => x.student == student).first()
    <-> * Submission.children

// or
//
// relation Submission.children * <-> ? Submission.parent = assignment.parent.submissions.filter(x => x.student == student).first()

// Option 2: datalog-style (with .notation)
//  + more declarative
//  - Submission.parent has * multiplicity (awkward to use)
//
// relation s1:Submission.parent <-> s2:Submission.children {
//   s2 = s1.assignment.parent.submissions 
//   s2 = s1.student.submissions
// }
  
// Option 3: datalog-style (with .notation) restricted
//  (evaluate all expressions, the intersection of all these values is the objects on the other side of the relation)
//  + more declarative
//  + allows for the .first() hack implicitly from the ?
//
// relation Submission.parent ? <-> Submission.children {
//   assignment.parent.submissions 
//   student.submissions
// }
  