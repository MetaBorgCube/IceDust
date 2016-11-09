module weblabgroupsubmissions

model

  entity Student {
  
  }
  
  entity Submission {
    grade : Float? = groupSubmission.grade (default) // if there is a group submission, use the group submission grade
  }
  
  entity Assignment {
  
  }
  
  relation Submission.assignment 1 <-> Assignment.submissions
  relation Submission.student 1 <-> Student.submissions
  
  entity Group {
  
  }
  
  relation Group.members <-> Student.groups
  
  entity GroupSubmission {
    grade : Float?
  }
  
  relation GroupSubmission.assignment 1 <-> Assignment.groupSubmissions
  relation GroupSubmission.group 1 <-> Group.submissions
  
  relation Submission.groupSubmission ? <-> * GroupSubmission.individualSubmissions // derive this
  
// Option 1: derived value expression
//
// relation Submission.groupSubmission ? = assignment.groupSubmissions.filter(x => x.group.members.contains(student))
// <-> * GroupSubmission.individualSubmissions 

// Option 2: datalog-style (with .notation)
//
// s:Submission.groupSubmission ? <-> * g:GroupSubmission.individualSubmissions {
//   g = s.assignment.groupSubmissions
//   g = s.student.groups.members.submissions
// }

// Option 3: datalog-style (with .notation) restricted
//
// Submission.groupSubmission ? <-> * GroupSubmission.individualSubmissions {
//   s.assignment.groupSubmissions
//   s.student.groups.members.submissions
// }
