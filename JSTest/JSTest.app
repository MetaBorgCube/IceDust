application JSTest

imports lib/icedust/newcrud-ui

imports lib/icedust/non-required-inputs

imports lib/icedust/Expressions

section  data

  init
  {
  }

section  model

  entity Person {
    boolean : Bool ( validate ( boolean != null , "" + "boolean" + " cannot be empty! " ) )
    function getBoolean ( ) : Bool
    {
      return this.boolean;
    }
    static function getBoolean ( en : Person ) : Bool
    {
      return if ( en == null ) ( null as Bool ) else en.getBoolean();
    }
    static function getBoolean ( entities : List<Person> ) : List<Bool>
    {
      return [ en.getBoolean() | en : Person in entities where en.getBoolean() != null ];
    }
    booleanOptional : Bool ( default= null )
    function getBooleanOptional ( ) : Bool
    {
      return this.booleanOptional;
    }
    static function getBooleanOptional ( en : Person ) : Bool
    {
      return if ( en == null ) ( null as Bool ) else en.getBooleanOptional();
    }
    static function getBooleanOptional ( entities : List<Person> ) : List<Bool>
    {
      return [ en.getBooleanOptional() | en : Person in entities where en.getBooleanOptional() != null ];
    }
    derived : String := calculateDerived()
    function getDerived ( ) : String
    {
      return this.derived;
    }
    static function getDerived ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getDerived();
    }
    static function getDerived ( entities : List<Person> ) : List<String>
    {
      return [ en.getDerived() | en : Person in entities where en.getDerived() != null ];
    }
    function calculateDerived ( ) : String
    {
      return Expressions.plus_String("You are ", Person.getPersonName(this));
    }
    derivedDefault : String ( default= null )
    function getDerivedDefault ( ) : String
    {
      return if ( this.derivedDefault != null ) this.derivedDefault else this.calculateDerivedDefault();
    }
    static function getDerivedDefault ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getDerivedDefault();
    }
    static function getDerivedDefault ( entities : List<Person> ) : List<String>
    {
      return [ en.getDerivedDefault() | en : Person in entities where en.getDerivedDefault() != null ];
    }
    function calculateDerivedDefault ( ) : String
    {
      return Expressions.plus_String("You are ", Person.getPersonName(this));
    }
    personName : String ( validate ( personName != null && personName.trim() != "" , "" + "personName" + " cannot be empty! " ) )
    function getPersonName ( ) : String
    {
      return this.personName;
    }
    static function getPersonName ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getPersonName();
    }
    static function getPersonName ( entities : List<Person> ) : List<String>
    {
      return [ en.getPersonName() | en : Person in entities where en.getPersonName() != null ];
    }
  }

section  ui

  define

  applicationmenu

  (

  )

  {

  navbaritem
    {
    navigate managePerson() [ ] { "Person" }
      }

  }

  page managePerson ( )
  {
  applicationmenu (  )
    <
    br
    />
    navigate createPerson() [ ] { "Create" }
    <
    br
    />
    for
    (
    entity
    :
    Person
    )
    {
    output ( entity.name )
    navigate person(entity) [ ] { "View" }
    " "
    navigate editPerson(entity) [ ] { "Edit" }
    " "
    submit
    (
    "Remove"
    ,
    removePerson(entity)
    )
    [
    ]
    <
    br
    />
    }
    action removePerson ( entity : Person )
    {
      entity.delete();
    }
  }

  page createPerson ( )
  {
  applicationmenu (  )
    <
    br
    />
    header
      {
      "Create"
        }
    var
    boolean
    :
    Bool
    var
    booleanOptional
    :
    Bool
    var
    derived
    :
    String
    var
    derivedDefault
    :
    String
    var
    personName
    :
    String
    form
      {
      "boolean :" input(boolean) <br/>
        "booleanOptional :" inputNonRequiredBool(booleanOptional) <br/>
        "derived :" input(derived) <br/>
        "derivedDefault :" input(derivedDefault) <br/>
        "personName :" input(personName) <br/>
        submit
        (
        "Save"
        ,
        save()
        )
        [
        ]
        }
    action save ( )
    {
      var temp := Person{boolean := boolean,
                         booleanOptional := booleanOptional,
                         derivedDefault := derivedDefault,
                         personName := personName} ;
      temp.save();
    }
    navigate managePerson() [ ] { "Back" }
  }

  page person ( temp : Person )
  {
  applicationmenu (  )
    <
    br
    />
    header
      {
      "View"
        }
    "boolean :" output(temp.getBoolean()) <br>
    "booleanOptional :" output(temp.getBooleanOptional()) <br>
    "derived :" output(temp.getDerived()) <br>
    "derivedDefault :" output(temp.getDerivedDefault()) <br>
    "personName :" output(temp.getPersonName()) <br>
    <
    hr
    />
    navigate managePerson() [ ] { "Back" }
  }

  page editPerson ( temp : Person )
  {
  applicationmenu (  )
    <
    br
    />
    header
      {
      "Edit"
        }
    var
    boolean
    :=
    temp.getBoolean()
    var
    booleanOptional
    :=
    temp.getBooleanOptional()
    var
    derivedDefault
    :=
    temp.derivedDefault
    var
    personName
    :=
    temp.getPersonName()
    form
      {
      "boolean :" input(boolean) <br/>
        "booleanOptional :" inputNonRequiredBool(booleanOptional) <br/>
        "derived :" output(temp.getDerived()) <br/>
        "derivedDefault :" input(derivedDefault) <br/>
        "personName :" input(personName) <br/>
        submit
        action
        {
          temp.boolean := boolean; temp.booleanOptional := booleanOptional; 
if(derivedDefault.trim() != "") {
  temp.derivedDefault := derivedDefault;
} else {
  temp.derivedDefault := null;
}
 temp.personName := personName;
          temp.save();
        }
        [
        ]
        {
        "Save"
        }
        }
    <
    hr
    />
    navigate managePerson() [ ] { "Back" }
  }