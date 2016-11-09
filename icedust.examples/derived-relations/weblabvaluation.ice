module weblabvaluation

model

  entity ChecklistValuation {
  
  }
  
  entity Person {
  
  }
  
  entity Submission {
  
  }
  
  relation ChecklistValuation.grader <-> Person.grading
  relation ChecklistValuation.submission <-> Submission.grading
  
  entity Assignment {
  
  }
  
  relation Assignment.submissions <-> Submission.assignment
  relation Person.submissions <-> Submission.person
  
  relation Submission.toGrade <-> Submission.dontcare // derive this
  
// Option 1: derived value expression
//
// relation Submission.toGrade = assignment.submissions.filter(x => x.grading.grader == person)
//   <-> ? Submission.dontcare
