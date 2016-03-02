module weblabtiny

// An oversimplified model of a grade calculation and course statistics tool in the university.
//
// It features:
//  - course statistics

model

  entity Student {
    name       : String
    
    passedCourses : Int = sum(enrollments.pass2)
  }
  
  entity Course {
    name       : String
    
    avgGrade   : Float?  = avg(enrollments.grade)
    passPerc   : Float?  = sum(enrollments.pass2) / count(enrollments) * 100.0
    numStudents: Int     = count(enrollments)
  }
  
  entity Enrollment {
    name       : String  = course.name + " " +student.name
    
    grade      : Float?
    pass       : Boolean = grade >= 5.5 <+ false
    pass2      : Int     = pass ? 1 : 0
  }
  
  relation Course.enrollments *  <-> 1 Enrollment.course
  relation Student.enrollments * <-> 1 Enrollment.student

data

  alice : Student {
    name = "Alice"
  }
  bob : Student {
    name = "Bob"
  }
  charlie : Student {
    name = "Charlie"
  }
  math : Course {
    name = "Math"
    enrollments = 
      enA {
        student = alice
        grade = 8.0
      },
      enB {
        student = bob
        grade = 9.5
      },
      enC {
        student = charlie
        grade = 5.0
      }
  }
  
execute

  math.name
  math.avgGrade
  math.passPerc
  math.numStudents
