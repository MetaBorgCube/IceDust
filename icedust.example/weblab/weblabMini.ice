module weblabMini

model

  entity Assignment (on-demand) {
    name     : String
    question : String?
    deadline : Datetime?
    minimum  : Float
    avgGrade : Float?    = avg(submissions.grade)
    passPerc : Float?    = count(submissions.filter(x=>x.pass)) / count(submissions)
  }
  
  entity Student {
    name     : String
  }
  
  entity Submission (incremental) {
    name     : String    = assignment.name + " " + student.name          (on-demand)
    answer   : String?
    deadline : Datetime? = assignment.deadline <+ parent.deadline        (default)
    finished : Datetime?
    onTime   : Boolean   = finished <= deadline <+ true
    grade    : Float?    = if(conj(children.pass)) avg(children.grade)   (default)
    pass     : Boolean   = grade >= assignment.minimum && onTime <+ false
    aboveAvg : Boolean   = grade >= assignment.avgGrade <+ false         (on-demand)
  }
  
  relation Submission.student    1 <-> * Student.submissions
  relation Submission.assignment 1 <-> * Assignment.submissions
  relation Assignment.parent     ? <-> * Assignment.children
  
  relation Submission.parent     ? =
    assignment.parent.submissions.find(x => x.student == student)
                                   <-> * Submission.children

data

  math:Assignment {
    name = "Math Assignments"
    minimum = 6.0
    children =
      exam {
        name = "Exam"
        question = "1+1=?"
        minimum = 5.0
      },
      practical {
        name = "Practical"
        question = "1/0=?"
        minimum = 5.0
        deadline = 2016-02-18 23:59:59
      }
  }
      
  alice : Student { // alice succeeds math
    name = "Alice"
    submissions =
      mathAlice {
        assignment = math
      },
      examAlice {
        assignment = exam
        answer = "Good"
        grade = 7.0
      },
      practicalAlice {
        assignment = practical
        answer = "Great"
        grade = 8.0
        finished = 2016-02-17 16:00:00
      }
  }
  
  bob : Student { // bob fails, because his exam is too low
    name = "Bob"
    submissions =
      mathBob {
        assignment = math
      },
      examBob {
        assignment = exam
        answer = "Bad"
        grade = 3.0
      },
      practicalBob {
        assignment = practical
        answer = "Perfect"
        grade = 10.0
        finished = 2016-02-17 16:00:00
      }
  }
    
execute

  "The average grade for math:"
  math.avgGrade
  "The pass percentage for math:"
  math.passPerc
