module weblab2

model // person

  entity Person {
    name : String
  }

data

  alice:Person{
    name = "Alice"
  }
  bob:Person{
    name = "Bob"
  }
  charles:Person{
    name = "Charles"
  }

model // course

  entity Course {
    name     : String
    key      : String
    code     : String
    fullname : String = code + ": " + name
  }

  entity CourseEdition {
    key      : String
    code     : String = course.code
    fullname : String = code + ": " + course.name + " (" + year + ")"
    year     : String
  }
  relation CourseEdition.students   <-> 1 StudentInCourse.course
  relation CourseEdition.course   1 <->   Course.editions
  
  entity StudentInCourse {
        
  }
  relation StudentInCourse             1 <->   Person.enrolled
  relation StudentInCourse.submissions   <-> 1 AssignmentSubmission.student

data

  programmingLanguages:Course{
    name = "Programming Languages"
    key = "PL"
    code = "PL"
    editions = 
      pl2015{
        key = "PL15"
        year = "2015"
        students =
          alicePl{
            person = alice
          },
          bobPl{
            person = bob
          }
      },
      pl2016{
        key = "PL15"
        year = "2016"
        students =
          alicePl2{
            person = alice
          },
          charlesPl{
            person = charles
          }
      }
  }

execute

  "Students of " + pl2015.fullname + ": "
  pl2015.students.person.name

model // assignments

  entity Assignment {
    key : String
    title : String
  }
  relation Assignment.root       1 = parent.root <+ this                       <-> Assignment
  relation Assignment.rootCourse ? = root.filter(:AssignmentCollection).course <-> CourseEdition.assignments

  entity AssignmentCollection extends Assignment {
    
  }
  relation AssignmentCollection.course      ? <-> ? CourseEdition.rootAssignment
  relation AssignmentCollection.assignments   <-> ? Assignment.parent
  
data

  pl2015Assignments:AssignmentCollection{
    course = pl2015
    key = "pl15a"
    title = "Assignments"
    assignments =
      pl15a1:AssignmentCollection{
        key = "pl15a1"
        title = "Week 1"
        assignments =
          pl15a11:Assignment{
            key = "pl15a11"
            title = "Assignment 1"
          },
          pl15a12:Assignment{
            key = "pl15a12"
            title = "Assignment 2"
          }
      },
      pl15a2:AssignmentCollection{
        key = "pl15a2"
        title = "Week 2"
        assignments =
          pl15a21:Assignment{
            key = "pl15a21"
            title = "Assignment 3"
          }
      }
  }
  
execute

  "Sub assignment root course name: "
  pl15a12.rootCourse.fullname

model // submisisons
  
  entity AssignmentSubmission {
    
  }
  relation AssignmentSubmission 1 <-> Assignment.submissions
  
  entity AssignmentCollectionSubmission extends AssignmentSubmission {
    
  }
  relation AssignmentCollectionSubmission.submissions = assignment.filter(:AssignmentCollection).assignments.submissions.filter(x => x.student == student)
    <-> ? AssignmentSubmission.parent

data

  :AssignmentCollectionSubmission{
    student = alicePl
    assignment = pl2015Assignments
  }
  :AssignmentCollectionSubmission{
    student = alicePl
    assignment = pl15a1
  }
  :AssignmentCollectionSubmission{
    student = alicePl
    assignment = pl15a2
  }
  :AssignmentSubmission{
    student = alicePl
    assignment = pl15a11
  }
  :AssignmentSubmission{
    student = alicePl
    assignment = pl15a12
  }
  alicePl15a21:AssignmentSubmission{
    student = alicePl
    assignment = pl15a21
  }

execute

  "Submission parent assignment name of " + alicePl15a21.assignment.title + ": "
  alicePl15a21.parent.assignment.title

model // submission grades

  entity GradingScheme {
    minimumToPass       : Float = 0.0  (default)
    passNSubAssignments : Int   = -1   (default)
    checkListWeight     : Float
    computedWeight      : Float = 1.0  (default)
    checkPercentage     : Float = 0.0  (default)
    customTotalWeight   : Float = -1.0 (default)
  }
  relation GradingScheme                  1 <-> ? Assignment
  relation GradingScheme.additionalGrades   <-> 1 AdditionalGradeDef
  
  entity SubmissionGrade {
    
  }
  relation SubmissionGrade.sub              1 <-> ? AssignmentSubmission.gradeData
  relation SubmissionGrade.assignment       1 = sub.assignment <-> Assignment
  relation SubmissionGrade.previousGrade    ? <-> ? SubmissionGrade.newerGrade
  relation SubmissionGrade.additionalGrades   <-> 1 AdditionalGrade

  entity AdditionalGradeDef {
    weight  : Float
    isBonus : Boolean
  }
  
  entity AdditionalGrade {
    
  }
  
model

  entity Notification {
    
  }

  entity ApplicationLog {
    
  }

  entity CheckList {
    
  }

  entity CheckListItem {
    
  }

  entity CheckListValuation {
    
  }

  entity CheckListItemValuation {
    
  }

  entity AssignmentRegirstrationKey {
    
  }

  entity Comment {
    
  }

  entity SubmissionComment extends Comment {
    
  }

  entity Point {
    
  }

  entity Correlation {
    
  }

  entity BasicAssignment extends Assignment {
    
  }

  entity BasicAssignmentSubmission extends AssignmentSubmission {
    
  }

  entity Question {
    
  }

  entity GradeOnlyQuestion extends Question {
    
  }

  entity CohortFileImport {
    
  }

  entity EducationCohort {
    
  }

  entity MentorGroup {
    
  }

  entity Education {
    
  }

  entity StudentInEducation {
    
  }

  entity RandomAssignmentCollection extends AssignmentCollection {
    
  }

  entity Database {
    
  }

  entity CourseRules {
    
  }

  entity CourseGroup {
    
  }

  entity CoursePresentation {
    
  }

  entity CourseRequest {
    
  }

  entity AbstractFile {
    
  }

  entity MetaData {
    
  }

  entity Directory extends AbstractFile {
    
  }

  entity DirectoryMetaData extends MetaData {
    
  }

  entity ProgrammingFile extends AbstractFile {
    
  }

  entity ProgrammingFileMetaData extends MetaData {
    
  }

  entity Language {
    
  }

  entity FileType {
    
  }

  entity FileSUbmissionQuestion extends Question {
    
  }

  entity FileSUbmissionAnswer extends BasicAssignmentSubmission {
    
  }

  entity GenerateQuestion extends Question {
    
  }

  entity GeneratedQuestionAnswer extends BasicAssignmentSubmission {
    
  }

  entity GradingWebhook {
    
  }

  entity GradeImport {
    
  }

  entity Institution {
    
  }

  entity MultipleChoiceQuestion extends Question {
    
  }

  entity Alternative {
    
  }

  entity MultipleChoiceAnswer extends BasicAssignmentSubmission {
    
  }

  entity NewsItem {
    
  }

  entity Note {
    
  }

  entity NoteStamp {
    
  }

  entity EssayQuestion extends Question {
    
  }

  entity EssayAnswer extends BasicAssignmentSubmission {
    
  }

  entity ReviewQuestion extends Question {
    
  }

  entity ReviewQuestionConfig {
    
  }

  entity ReviewAnswer extends BasicAssignmentSubmission {
    
  }

  entity Event {
    
  }

  entity ProgrammingQuestion extends Question {
    
  }

  entity DataFile {
    
  }

  entity WebProgrammingQuestion extends Question {
    
  }

  entity ProgrammingAnswer extends BasicAssignmentSubmission {
    
  }

  entity WebProgrammingAnswer extends BasicAssignmentSubmission {
    
  }

  entity ProgramRun {
    
  }

  entity StudentGroup {
    
  }

  entity TextChange {
    
  }
  