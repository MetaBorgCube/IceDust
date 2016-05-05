application NewCrud

imports lib/icedust/newcrud-ui

imports lib/icedust/non-required-inputs

imports lib/icedust/Expressions

section  data

  init
  {
  }

section  model

  entity Person {
    nickname : String ( default= null )
    function getNickname ( ) : String
    {
      return this.nickname;
    }
    static function getNickname ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getNickname();
    }
    static function getNickname ( entities : List<Person> ) : List<String>
    {
      return [ en.getNickname() | en : Person in entities where en.getNickname() != null ];
    }
    nonReqBool : Bool ( default= null )
    function getNonReqBool ( ) : Bool
    {
      return this.nonReqBool;
    }
    static function getNonReqBool ( en : Person ) : Bool
    {
      return if ( en == null ) ( null as Bool ) else en.getNonReqBool();
    }
    static function getNonReqBool ( entities : List<Person> ) : List<Bool>
    {
      return [ en.getNonReqBool() | en : Person in entities where en.getNonReqBool() != null ];
    }
    nonReqDatetime : DateTime ( default= null )
    function getNonReqDatetime ( ) : DateTime
    {
      return this.nonReqDatetime;
    }
    static function getNonReqDatetime ( en : Person ) : DateTime
    {
      return if ( en == null ) ( null as DateTime ) else en.getNonReqDatetime();
    }
    static function getNonReqDatetime ( entities : List<Person> ) : List<DateTime>
    {
      return [ en.getNonReqDatetime() | en : Person in entities where en.getNonReqDatetime() != null ];
    }
    nonReqFloat : Float ( default= null )
    function getNonReqFloat ( ) : Float
    {
      return this.nonReqFloat;
    }
    static function getNonReqFloat ( en : Person ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getNonReqFloat();
    }
    static function getNonReqFloat ( entities : List<Person> ) : List<Float>
    {
      return [ en.getNonReqFloat() | en : Person in entities where en.getNonReqFloat() != null ];
    }
    nonReqInt : Int ( default= null )
    function getNonReqInt ( ) : Int
    {
      return this.nonReqInt;
    }
    static function getNonReqInt ( en : Person ) : Int
    {
      return if ( en == null ) ( null as Int ) else en.getNonReqInt();
    }
    static function getNonReqInt ( entities : List<Person> ) : List<Int>
    {
      return [ en.getNonReqInt() | en : Person in entities where en.getNonReqInt() != null ];
    }
    reqBool : Bool ( default= null )
    function getReqBool ( ) : Bool
    {
      return this.reqBool;
    }
    static function getReqBool ( en : Person ) : Bool
    {
      return if ( en == null ) ( null as Bool ) else en.getReqBool();
    }
    static function getReqBool ( entities : List<Person> ) : List<Bool>
    {
      return [ en.getReqBool() | en : Person in entities where en.getReqBool() != null ];
    }
    reqDatetime : DateTime ( default= null )
    function getReqDatetime ( ) : DateTime
    {
      return this.reqDatetime;
    }
    static function getReqDatetime ( en : Person ) : DateTime
    {
      return if ( en == null ) ( null as DateTime ) else en.getReqDatetime();
    }
    static function getReqDatetime ( entities : List<Person> ) : List<DateTime>
    {
      return [ en.getReqDatetime() | en : Person in entities where en.getReqDatetime() != null ];
    }
    reqFloat : Float ( default= null )
    function getReqFloat ( ) : Float
    {
      return this.reqFloat;
    }
    static function getReqFloat ( en : Person ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getReqFloat();
    }
    static function getReqFloat ( entities : List<Person> ) : List<Float>
    {
      return [ en.getReqFloat() | en : Person in entities where en.getReqFloat() != null ];
    }
    reqInt : Int ( default= null )
    function getReqInt ( ) : Int
    {
      return this.reqInt;
    }
    static function getReqInt ( en : Person ) : Int
    {
      return if ( en == null ) ( null as Int ) else en.getReqInt();
    }
    static function getReqInt ( entities : List<Person> ) : List<Int>
    {
      return [ en.getReqInt() | en : Person in entities where en.getReqInt() != null ];
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
  var temp := Person{}
    header
      {
      "Create "
        output ( temp.name )
        }
    form
      {
      <
        fieldset
        >
        <
        legend
        >
        output ( "Details" )
        </
        legend
        >
        <
        table
        >
        derive editRows from temp for ( nickname , nonReqBool , nonReqDatetime , nonReqFloat , nonReqInt , reqBool , reqDatetime , reqFloat , reqInt )
        </
        table
        >
        </
        fieldset
        >
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
      temp.save();
      return managePerson();
    }
  }

  define

  page

  person

  (

  arg : Person

  )

  {

  derive viewPage from arg

  }

  define

  page

  editPerson

  (

  arg : Person

  )

  {

  main (  )

  define

  body

  (

  )

  {

  header
    {
    "Edit "
      output ( arg.name )
      }

  form
    {
    <
      fieldset
      >
      <
      legend
      >
      output ( "Details" )
      </
      legend
      >
      <
      table
      >
      derive editRows from arg for ( nickname , nonReqBool , nonReqDatetime , nonReqFloat , nonReqInt , reqBool , reqDatetime , reqFloat , reqInt )
      </
      table
      >
      </
      fieldset
      >
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
    arg.save();
    return managePerson();
  }

  }

  }