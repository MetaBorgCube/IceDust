module weblabsubmissions

model

  entity Assignment {
    name : String
    avgGrade : Float? = avg(submissions.grade)
  }

  entity Submission {
    name : String = assignment.name + " " + student.name
    grade : Float? = avg(children.grade) (default)
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

data

  alice:Student{
    name = "Alice"
  }
  bob:Student{
    name = "Bob"
  }
  charles:Student{
    name = "Charles"
  }
  
  assignment:Assignment {
    name = "Math"
    submissions =
      {
        grade = 10.0 // override final grade of alice
        student = alice
      },
      {
        student = bob
      },
      {
        student = charles
      }
    children =
      {
        name = "exam"
        submissions =
          {
            grade = 8.0
            student = alice
          },
          {
            grade = 8.0
            student = bob
          },
          {
            grade = 6.5
            student = charles
          }
      },
      {
        name = "lab"
        submissions =
          {
            grade = 8.0
            student = alice
          },
          {
            grade = 8.0
            student = bob
          },
          {
            grade = 5.5
            student = charles
          }
      }
  }
  
execute

  assignment.avgGrade // only works with incremental (uses Submission.children) // should be 8.0
  
