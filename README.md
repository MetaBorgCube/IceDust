# Relational programming

This is an information system modeling language; a declarative specification language with first class relations and derived values.

## Example

```
module students

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
```

The example describes a system in the `model` section with students, courses and enrollment-relations between students and courses. The `pass` attribute in Enrollment and the `averageGrade` attribute in Course are _derived values_. Based on the compiler settings these are eagerly, lazily or eventually computed.

The `data` section describes the default data for the system, and the `execute` section triggers computation for the Java compiler.

The type system is aware of _multiplicities_ (the number of values an expression can yield). Expression `grade >= 6 <+ false` has a multiplicity of [1,1]. Since `grade` has multiplicity [0,1] `grade >= 5.5` has multiplicity [0,1]. The choice operator (`<+`) takes the second operand if the first one returns no values. Thus `grade >= 5.5 <+ false` has multiplicity [1,1].

## Getting the Editor

Download from http://buildfarm.metaborg.org/job/relations-eclipsegen/

## Building the Editor (in Spoofax)

1. Get Spoofax from http://buildfarm.metaborg.org/job/spoofax-master/lastSuccessfulBuild/artifact/dist/
2. Check out this git repo
3. Build the editor project in [relations](relations)

Building the editor in Spoofax does not have both issues listed for the Download.


## Try building the examples

1. Check out this git repo
2. See the [relations.examples](relations.examples)

### Java backend

To use the Java backend use the menu `Spoofax > Generation > to Java > Calculate on Read > Generate, Compile and Execute`.

Or use `Spoofax > Generation > to Java > Calculate on Read > Generate` and build the generated Java (make sure the Java files are on the classpath and that your eclipse project has the Java nature and Java builder).

### WebDSL backend

Compiling to WebDSL requires you to have the Relations file the same name as the project name (case sensitive) and to be in the root folder of the project:

```
Demo (project name)
Demo/Demo.rel (relations file)
Demo/Demo.app (generated WebDSL file)
```

And `Demo.rel`:

```
module Demo

model

  //...
```

2. Use `Spoofax > Generation > to WebDSL > Calculate on Read > Generate, Standalone Application` to generate the `.app` file.
3. Import the project in the [WebDSL editor](http://buildfarm.metaborg.org/job/webdsl-eclipsegen/).
4. Convert the project to a WebDSL project by right-clicking the project in the WebDSL editor.
5. Press `Cmd + Alt + B` in the `.app` file to trigger the WebDSL compiler, the compiler will build the project and automatically launch a webserver and open the main web page of the application.
