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

  relation Submission.parent ? = assignment.parent.submissions.filter(x => x.student == student).first()
    <-> * Submission.children

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
  
