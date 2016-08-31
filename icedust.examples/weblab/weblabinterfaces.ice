module weblabinterfaces

model

  interface Assignment {
    name : String
    size : Int
  }

  entity AssignmentCollection extends Assignment {
    size : Int = 1 + count(assignments)
  }

  entity BasicAssignment extends Assignment {
    size : Int = 1
  }
  
  relation AssignmentCollection <-> ? Assignment.parent

data

  math:AssignmentCollection{
    name = "Math"
    assignments =
      lab : AssignmentCollection{
        name = "Lab"
        assignments =
          lab1 : BasicAssignment{
            name = "Lab1"
          },
          lab2 : BasicAssignment{
            name = "Lab2"
          }
      },
      exam: BasicAssignment{
        name = "Lab"
      }
  }

execute

  math.size

  