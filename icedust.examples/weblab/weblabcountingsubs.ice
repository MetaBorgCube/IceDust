module weblabcountingsubs

model

  entity Assignment {
    name : String
    avgGrade : Float? = avg(countingSubs.grade)
  }

  entity Submission {
    name : String = assignment.name + student.name
    grade : Float?
  }

  entity Student {
    name : String
    forGrade : Boolean = false (default)
  }

  relation Assignment.submissions <-> 1 Submission.assignment

  relation Student.submissions <-> 1 Submission.student

  relation Assignment.countingSubs = submissions.filter(x => x.student.forGrade)
    <-> ? Submission.dontcare

data

  alice:Student{
    name = "alice"
    forGrade = true
  }
  bob:Student{
    name = "bob"
  }
  charles:Student{
    name = "charles"
    forGrade = true
  }
  
  assignment:Assignment{
    name = "assignment"
    submissions =
      {
        student = alice
        grade = 10.0
      },
      {
        student = bob
        grade = 10.0
      },
      {
        student = charles
        grade = 8.0
      }
  }
  
execute

  assignment.countingSubs.name
  assignment.avgGrade // should be 9.0 as bob does not count
