# Relational programming

This is an information system modeling language; a declarative specification language with first class relations and derived values.

## Example

```
module students

model
	
  entity Student {
    name         : String
  }
  	
  entity Course {
    name         : String
    averageGrade : Int? = avg(enrollment.grade)
  }
  
  relation Enrollment {
    Student *
    Course  *
    
    grade      : Int?
    pass       : Boolean = grade >= 6 <+ false
  }
	
data

  Student alice   { name="Alice" }
  Student bob     { name="Bob" }
  Student charlie { name="Charlie" }
  
  Course  math { name="Mathematics" }
  
  Enrollment { student:alice   course:math grade=9 }
  Enrollment { student:bob     course:math grade=5 }
  Enrollment { student:charlie course:math }
  
execute

  "Did alice pass math?"
  alice.enrollment.pass
  
  ""
  "The average grade at Mathematics:"
  math.averageGrade
  
  ""
  "Bob's classmates (including self):"
  bob.course.student.name
```

The example describes a system in the `model` section with students, courses and enrollment-relations between students and courses. The `pass` attribute in Enrollment and the `averageGrade` attribute in Course are _derived values_. Based on the compiler settings these are eagerly, lazily or eventually computed.

The `data` section describes the default data for the system, and the `execute` section triggers computation for the Java compiler.

The type system is aware of _multiplicities_ (the number of values an expression can yield). Expression `grade >= 6 <+ false` has a multiplicity of [1,1]. Since `grade` has multiplicity [0,1] `grade >= 6` has multiplicity [0,1]. The choice operator (`<+`) takes the second operand if the first one returns no values. Thus `grade >= 6 <+ false` has multiplicity [1,1].

## Getting the Editor

Download from http://buildfarm.metaborg.org/job/relations-eclipsegen/

Known issues:

* Generation > Execute Java does not show any output on the console (Generation > Generate Java and then running the Java program from Eclipse works fine)
* The WebDSL editor fails to analyze its files when the Relation Language Editor is also installed (building the generated WebDSL files works fine)

## Building the Editor (in Spoofax)

You can avoid the above known issues by building the editor yourself.

1. Get Spoofax from http://buildfarm.metaborg.org/job/spoofax-master/lastSuccessfulBuild/artifact/dist/ (Only Java backend)
   Or get WebDSL+Spoofax from http://buildfarm.metaborg.org/job/webdsl-eclipsegen/ (Works for both Java and WebDSL backend)
2. Check out this git repo
3. Build the editor project in [relations](relations)

Building the editor in Spoofax does not have both issues listed for the Download.


## Try building the examples

1. Check out this git repo
2. See the [relations-examples](relations-examples)

### Java backend

To use the Java backend use Generation > Execute Java (if you built the editor in Spoofax).

Or use Generation > Generate Java and build the generated Java (make sure the Java files are on the classpath and that your eclipse project has the Java nature and Java builder) (if you have downloaded the editor).

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

2. Use `Generation > Generate WebDSL eager` to generate the `.app` file.
3. And then right click the project `Convert to a WebDSL project`.
4. Press `Cmd + Alt + B` in the `.app` file to trigger the WebDSL compiler.
