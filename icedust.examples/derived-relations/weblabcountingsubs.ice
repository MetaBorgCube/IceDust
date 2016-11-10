module weblabcountingsubs

model

  entity Assignment {
    name : String
  }

  entity Submission {
    name : String
  }

  entity StudentInCourse {
    name : String
    forGrade : Boolean
  }

  relation Assignment.submissions <-> 1 Submission.assignment

  relation StudentInCourse.submissions <-> 1 Submission.student

//  relation Assignment.countingSubs <-> ? Submission.dontcare // derive this
  
// Option 1: derived value expression

  relation Assignment.countingSubs = submissions//.filter(x => x.student.forGrade)
    <-> ? Submission.dontcare

// Option 2: datalog-style (with.notation)
//
// a:Assignment.countingSubs <-> ? s:Submission.dontcare {
//   s = a.submissions.filter(x => x.student.forGrade)
// }

// Option 2: datalog-style (with.notation) restricted
//
// Assignment.countingSubs <-> ? Submission.dontcare {
//   submissions.filter(x => x.student.forGrade)
// }