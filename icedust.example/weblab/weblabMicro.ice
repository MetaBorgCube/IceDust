module weblabMicro

model
  
  entity Student { }
  
  entity Submission (incremental) {
    pass     : Boolean = grade >= 5.5 <+ false
    grade    : Float?  = if(conj(children.pass)) avg(children.grade)
                         else                    no value (default)
    aboveAvg : Boolean = grade >= assignment.avgGrade <+ false (on-demand)
  }

  entity Assignment {
    avgGrade : Float?  = avg(submissions.grade) (on-demand)
  }
  
  relation Submission.student    1 <-> * Student.submissions
  relation Submission.assignment 1 <-> * Assignment.submissions
  relation Assignment.parent     ? <-> * Assignment.children
  
  relation Submission.parent     ? =
    assignment.parent.submissions.find(x => x.student == student)
                                   <-> * Submission.children

data

  math:Assignment {
    children =
      lab {
        children = 
          lab1{},
          lab2{}
      },
      exam {
      }
  }
      
  alice : Student { // alice succeeds math
    submissions =
      mathAlice {
        assignment = math
      },
      labAlice {
        assignment = lab
      },
      lab1Alice {
        assignment = lab1
        grade = 10.0
      },
      lab2Alice {
        assignment = lab2
        grade = 6.0
      },
      examAlice {
        assignment = exam
        grade = 7.0
      }
  }
  
  bob : Student { // bob fails, because one of his labs is too low
    submissions =
      mathBob {
        assignment = math
      },
      labBob {
        assignment = lab
      },
      lab1Bob {
        assignment = lab1
        grade = 8.0
      },
      lab2Bob {
        assignment = lab2
        grade = 3.0
      },
      examBob {
        assignment = exam
        grade = 9.0
      }
  }
    
execute

  "The average grade for math:"
  math.avgGrade
