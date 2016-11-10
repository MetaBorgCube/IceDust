module weblabvaluation

model

  entity ChecklistValuation {
  
  }
  
  entity Person {
  
  }
  
  entity Submission {
  
  }
  
  relation ChecklistValuation.grader 1 <-> Person.grading
  relation ChecklistValuation.submission <-> 1 Submission.grading
  relation ChecklistValuation.submission2 <-> 1 Submission.checking
  
  entity Assignment {
  
  }
  
  relation Assignment.submissions <-> Submission.assignment
  relation Person.submissions <-> 1 Submission.person
  
  entity AssignmentPerson { // derive this
    progress: Float// = ...
  }
  
  relation AssignmentPerson.assignment <-> Assignment.assignmentPerson // derive this
  relation AssignmentPerson.person <-> Person.assignmentPerson // derive this
  
//  relation AssignmentPerson.toGrade <-> Submission.dontcare // derive this
  relation AssignmentPerson.toGradeCompleted <-> Submission.dontcare2
  
// TODO: skip, because Assignment.findChecklistValuations(p:Person) does not have an abstraction AssignmentPerson
  
// Option 1: derived value expression

 relation Submission.toGrade = assignment.submissions.filter(x => x.grading.grader == person)
   <-> ? Submission.dontcare
