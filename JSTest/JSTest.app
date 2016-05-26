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
    personName
    :
    String
    form
      {
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
      var temp := Person{personName := personName} ;
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
    "derived :" output(temp.getDerived()) <br>
    "personName :" output(temp.getPersonName()) <br>
    <
    hr
    />
    navigate managePerson() [ ] { "Back" }
  }

  page editPerson ( temp : Person )
  {
  	includeJS("javascript-lib.js")
  applicationmenu (  )
    <
    br
    />
    header
      {
      "Edit"
        }
    var
    personName
    :=
    temp.getPersonName()
    form
      {
      "derived :" <div id="derived">output(temp.getDerived())</div> <br/>
        "personName :" <div id="personName" class="input" data-flows-to="derived">input(personName)</div> <br/>
        submit
        action
        {
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