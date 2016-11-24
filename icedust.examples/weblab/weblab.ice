module weblab

// A simplified model of a grade calculation and course statistics tool in the university.
//
// It features:
//  - weighted average grades, for example the course grade is 70% exam and 30% practical
//  - optional minimum grades, for example the exam and practical both need to be at least a 5.0 before a course grade is given
//  - optional deadlines and deadline extensions, if an assignment is turned in after a deadline but before the deadline extension a grade penalty is applied. If the assignment is turned in after the deadline extension, no grade.
//  - personal deadlines and deadline extensions, teachers can assign students a personal deadline
//  - assignment and course statistics

model

  entity Student {
    name       : String
    
    passedCourses : Int = sum(enrollments.pass2)
  }
  
  entity Course {
    name       : String
    
    avgGrade   : Float?  = assignment.avgGrade
    passPerc   : Float?  = assignment.passPerc
    numStudents: Int     = count(enrollments)
    
    summary    : String  = "The course " + name + " has " + numStudents as String + " students, " +
                           ("has a pass percentage of " + passPerc as String + "%" <+ "has no passing students") + ", and " +
                           ("passing students have an average grade of " + avgGrade as String + "." <+ "has no average grade.")
  }
  
  entity Enrollment {
    name       : String  = course.name + " " +student.name
    
    grade      : Float?  = submission.grade
    pass       : Boolean = submission.pass
    pass2      : Int     = pass ? 1 : 0
  }
  
  relation Course.enrollments *  <-> 1 Enrollment.course
  relation Student.enrollments * <-> 1 Enrollment.student
  
  entity Assignment {
    name       : String
    question   : String?
    minimum    : Float?
    weight     : Float   = 1.0 (default)
    deadline   : Datetime? // deadline is optional
    extension  : Datetime? // deadline extension is optional
    latePenalty: Float?    // penalty for using the full deadline extension
    
    avgGrade   : Float?  = avg(submissions.grade)
    passPerc   : Float?  = sum(submissions.passInt) / count(submissions) * 100.0
  }
  
  entity Submission {
    name       : String  = assignment.name + " " + student.name
    answer     : String?
    date       : Datetime?
    
    deadline   : Datetime? = assignment.deadline (default) // teacher can overrride the deadline for a specific student
    extension  : Datetime? = assignment.extension (default) // teacher can override the deadline extension for a specific student
    
    onTime     : Boolean = date <= deadline
                           <+
                           count(deadline)==0 || count(date)==1 // no deadline is always on time

    onExtension: Boolean = !onTime && date <= extension
                           <+
                           false // no extension means late, no submission date also means late

    latePenalty: Float   = if(onExtension)
                             (date - deadline) / (extension - deadline) * assignment.latePenalty
                           else
                             0.0
                           <+
                           0.0
    
    childGrade : Float?  = sum(children.gradeWeighted) / sum(assignment.children.weight)
    baseGrade  : Float?  = switch {
                             case childPass => childGrade
                             default        => no value // if one of child assignments not passed, no grade in the parent assignment
                           } (default)                  // if this a leaf assginment, then the grade is entered here
    grade      : Float?  = switch {
                             case onTime      => baseGrade
                             case onExtension => baseGrade - latePenalty
                             default          => no value
                           }
    gradeWeighted : Float? = grade * assignment.weight
    
    childPass  : Boolean = conj(children.pass)
    pass       : Boolean = grade >= (assignment.minimum<+0.0) && childPass <+ false
  
    passInt    : Int     = if(pass) 1 else 0
    best       : Boolean = grade == max(assignment.submissions.grade) <+ false
  }
  
  relation Assignment.parent     ? (ordered) <-> * (ordered) Assignment.children
  relation Submission.student    1 <-> * Student.submissions
  relation Submission.assignment 1 <-> * Assignment.submissions
  
  relation Course.assignment     1 <-> ? Assignment.course
  relation Enrollment.submission 1 <-> ? Submission.enrollment
     
  relation Submission.children * (ordered) = assignment.children.submissions.filter(x => x.student == student)
     <-> ? (ordered) Submission.parent

  relation Assignment.next ? = parent.children.elemAt(parent.children.indexOf(this) + 1)
     <-> ? Assignment.previous
     
  relation Submission.next ? = parent.children.elemAt(parent.children.indexOf(this) + 1)
     <-> ? Submission.previous

data

  alice : Student {
    name = "Alice"
    submissions =
      mathAlice {
        assignment = mathAssignment
      },
      examAlice {
        assignment = exam
        answer = "Good"
        baseGrade = 7.0
      },
      practicalAlice {
        assignment = practical
        answer = "Great"
        baseGrade = 8.0
        date = 2016-02-17 16:00:00
      }
  }
  bob : Student {
    name = "Bob"
    submissions =
      mathBob {
        assignment = mathAssignment
      },
      examBob {
        assignment = exam
        answer = "Bad"
        baseGrade = 3.0
      },
      practicalBob {
        assignment = practical
        answer = "Perfect"
        baseGrade = 10.0
        date = 2016-02-17 16:00:00
      }
  }
  charlie : Student {
    name = "Charlie"
    submissions =
      mathCharlie {
        assignment = mathAssignment
      },
      examCharlie {
        assignment = exam
        answer = "Great"
        baseGrade = 8.0
      },
      practicalCharlie {
        assignment = practical
        answer = "Sufficient"
        baseGrade = 6.0
        date = 2016-02-20 16:00:00
      }
  }
  dave : Student {
    name = "Dave"
    submissions =
      mathDave {
        assignment = mathAssignment
      },
      examDave {
        assignment = exam
        answer = "Great"
        baseGrade = 8.0
      },
      practicalDave {
        assignment = practical
        answer = "Great"
        baseGrade = 8.0
        date = 2016-02-27 16:00:00
      }
  }
  eve : Student {
    name = "Eve"
    submissions =
      mathEve {
        assignment = mathAssignment
      },
      examEve {
        assignment = exam
        answer = "Great"
        baseGrade = 8.0
      },
      practicalEve {
        assignment = practical
        answer = "Near Perfect"
        baseGrade = 9.0
        date = 2016-02-27 16:00:00
        deadline = 2016-02-27 23:59:59
      }
  }
  math : Course {
    name = "Math"
    assignment = 
      mathAssignment {
        name = "Math Assignments"
        minimum = 6.0
        children =
          exam {
            name = "Exam"
            question = "1+1=?"
            minimum = 5.0
            weight = 70.0
          },
          practical {
            name = "Practical"
            question = "1/0=?"
            minimum = 5.0
            weight = 30.0
            deadline = 2016-02-18 23:59:59
            extension = 2016-02-20 23:59:59
            latePenalty = 2.0
          }
      }
    enrollments = 
      enA { // alice succeeds math
        student = alice
        submission = mathAlice
      },
      enB { // bob fails, because his exam is too low
        student = bob
        submission = mathBob
      },
      enC { // charlie fails, because with the penalty for his practical his practical is too low
        student = charlie
        submission = mathCharlie
      },
      enD { // dave fails, because his practical is submitted after the deadline extension
        student = dave
        submission = mathDave 
      },
      enE { // eve succeeds, as she got a deadline extension
        student = eve
        submission = mathEve 
      }
  }
  
execute

  math.summary // should be 40% passing and with an average of 7.8
