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
      return Expressions.plus_String(Expressions.plus_String(Person.getNickname2(this), " "), ( Expressions.choice_One_One(Person.getNickname(this), "") as String ));
    }
    derivedDefault : String ( validate ( derivedDefault != null , "" + "derivedDefault" + " cannot be empty! " ) )
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
      return Expressions.plus_String(Expressions.plus_String(Person.getNickname2(this), " "), ( Expressions.choice_One_One(Person.getNickname(this), "") as String ));
    }
    derivedDefaultOption : String ( default= null )
    function getDerivedDefaultOption ( ) : String
    {
      return if ( this.derivedDefaultOption != null ) this.derivedDefaultOption else this.calculateDerivedDefaultOption();
    }
    static function getDerivedDefaultOption ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getDerivedDefaultOption();
    }
    static function getDerivedDefaultOption ( entities : List<Person> ) : List<String>
    {
      return [ en.getDerivedDefaultOption() | en : Person in entities where en.getDerivedDefaultOption() != null ];
    }
    function calculateDerivedDefaultOption ( ) : String
    {
      return Expressions.plus_String(Expressions.plus_String(Person.getNickname2(this), " "), ( Expressions.choice_One_One(Person.getNickname(this), "") as String ));
    }
    derivedInt : Int := calculateDerivedInt()
    function getDerivedInt ( ) : Int
    {
      return this.derivedInt;
    }
    static function getDerivedInt ( en : Person ) : Int
    {
      return if ( en == null ) ( null as Int ) else en.getDerivedInt();
    }
    static function getDerivedInt ( entities : List<Person> ) : List<Int>
    {
      return [ en.getDerivedInt() | en : Person in entities where en.getDerivedInt() != null ];
    }
    function calculateDerivedInt ( ) : Int
    {
      return Person.getReqInt(this);
    }
    derivedIntDefault : Int ( validate ( derivedIntDefault != null , "" + "derivedIntDefault" + " cannot be empty! " ) )
    function getDerivedIntDefault ( ) : Int
    {
      return if ( this.derivedIntDefault != null ) this.derivedIntDefault else this.calculateDerivedIntDefault();
    }
    static function getDerivedIntDefault ( en : Person ) : Int
    {
      return if ( en == null ) ( null as Int ) else en.getDerivedIntDefault();
    }
    static function getDerivedIntDefault ( entities : List<Person> ) : List<Int>
    {
      return [ en.getDerivedIntDefault() | en : Person in entities where en.getDerivedIntDefault() != null ];
    }
    function calculateDerivedIntDefault ( ) : Int
    {
      return Person.getReqInt(this);
    }
    derivedIntDefaultOption : Int ( default= null )
    function getDerivedIntDefaultOption ( ) : Int
    {
      return if ( this.derivedIntDefaultOption != null ) this.derivedIntDefaultOption else this.calculateDerivedIntDefaultOption();
    }
    static function getDerivedIntDefaultOption ( en : Person ) : Int
    {
      return if ( en == null ) ( null as Int ) else en.getDerivedIntDefaultOption();
    }
    static function getDerivedIntDefaultOption ( entities : List<Person> ) : List<Int>
    {
      return [ en.getDerivedIntDefaultOption() | en : Person in entities where en.getDerivedIntDefaultOption() != null ];
    }
    function calculateDerivedIntDefaultOption ( ) : Int
    {
      return Person.getNonReqInt(this);
    }
    derivedIntOptional : Int := calculateDerivedIntOptional()
    function getDerivedIntOptional ( ) : Int
    {
      return this.derivedIntOptional;
    }
    static function getDerivedIntOptional ( en : Person ) : Int
    {
      return if ( en == null ) ( null as Int ) else en.getDerivedIntOptional();
    }
    static function getDerivedIntOptional ( entities : List<Person> ) : List<Int>
    {
      return [ en.getDerivedIntOptional() | en : Person in entities where en.getDerivedIntOptional() != null ];
    }
    function calculateDerivedIntOptional ( ) : Int
    {
      return Person.getNonReqInt(this);
    }
    derivedOptional : String := calculateDerivedOptional()
    function getDerivedOptional ( ) : String
    {
      return this.derivedOptional;
    }
    static function getDerivedOptional ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getDerivedOptional();
    }
    static function getDerivedOptional ( entities : List<Person> ) : List<String>
    {
      return [ en.getDerivedOptional() | en : Person in entities where en.getDerivedOptional() != null ];
    }
    function calculateDerivedOptional ( ) : String
    {
      return Expressions.plus_String(Expressions.plus_String(Person.getNickname2(this), " "), ( Expressions.choice_One_One(Person.getNickname(this), "") as String ));
    }
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
    nickname2 : String ( validate ( nickname2 != null , "" + "nickname2" + " cannot be empty! " ) )
    function getNickname2 ( ) : String
    {
      return this.nickname2;
    }
    static function getNickname2 ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getNickname2();
    }
    static function getNickname2 ( entities : List<Person> ) : List<String>
    {
      return [ en.getNickname2() | en : Person in entities where en.getNickname2() != null ];
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
    reqBool : Bool ( validate ( reqBool != null , "" + "reqBool" + " cannot be empty! " ) )
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
    reqDatetime : DateTime ( validate ( reqDatetime != null , "" + "reqDatetime" + " cannot be empty! " ) )
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
    reqFloat : Float ( validate ( reqFloat != null , "" + "reqFloat" + " cannot be empty! " ) )
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
    reqInt : Int ( validate ( reqInt != null , "" + "reqInt" + " cannot be empty! " ) )
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
  header
    {
    "Create"
      }
    var
    derivedDefault
    :
    String
    var
    derivedDefaultOption
    :
    String
    var
    derivedIntDefault
    :
    Int
    var
    derivedIntDefaultOption
    :
    Int
    var
    nickname
    :
    String
    var
    nickname2
    :
    String
    var
    nonReqBool
    :
    Bool
    var
    nonReqDatetime
    :
    DateTime
    var
    nonReqFloat
    :
    Float
    var
    nonReqInt
    :
    Int
    var
    reqBool
    :
    Bool
    var
    reqDatetime
    :
    DateTime
    var
    reqFloat
    :
    Float
    var
    reqInt
    :
    Int
    form
      {
      "derivedDefault :" input(derivedDefault) <br/>
        "derivedDefaultOption :" input(derivedDefaultOption) <br/>
        "derivedIntDefault :" input(derivedIntDefault) <br/>
        "derivedIntDefaultOption :" input(derivedIntDefaultOption) <br/>
        "nickname :" input(nickname) <br/>
        "nickname2 :" input(nickname2) <br/>
        "nonReqBool :" inputNonRequiredBool(nonReqBool) <br/>
        "nonReqDatetime :" input(nonReqDatetime) <br/>
        "nonReqFloat :" input(nonReqFloat) <br/>
        "nonReqInt :" input(nonReqInt) <br/>
        "reqBool :" input(reqBool) <br/>
        "reqDatetime :" input(reqDatetime) <br/>
        "reqFloat :" input(reqFloat) <br/>
        "reqInt :" input(reqInt) <br/>
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
      var temp := Person{derivedDefault := derivedDefault,
                         derivedDefaultOption := derivedDefaultOption,
                         derivedIntDefault := derivedIntDefault,
                         derivedIntDefaultOption := derivedIntDefaultOption,
                         nickname := nickname,
                         nickname2 := nickname2,
                         nonReqBool := nonReqBool,
                         nonReqDatetime := nonReqDatetime,
                         nonReqFloat := nonReqFloat,
                         nonReqInt := nonReqInt,
                         reqBool := reqBool,
                         reqDatetime := reqDatetime,
                         reqFloat := reqFloat,
                         reqInt := reqInt} ;
      temp.save();
      return managePerson();
    }
    navigate managePerson() [ ] { "Back" }
  }

  page person ( temp : Person )
  {
  header
    {
    "View"
      }
    "derived :" output(temp.getDerived()) <br>
    "derivedDefault :" output(temp.getDerivedDefault()) <br>
    "derivedDefaultOption :" output(temp.getDerivedDefaultOption()) <br>
    "derivedInt :" output(temp.getDerivedInt()) <br>
    "derivedIntDefault :" output(temp.getDerivedIntDefault()) <br>
    "derivedIntDefaultOption :" output(temp.getDerivedIntDefaultOption()) <br>
    "derivedIntOptional :" output(temp.getDerivedIntOptional()) <br>
    "derivedOptional :" output(temp.getDerivedOptional()) <br>
    "nickname :" output(temp.getNickname()) <br>
    "nickname2 :" output(temp.getNickname2()) <br>
    "nonReqBool :" output(temp.getNonReqBool()) <br>
    "nonReqDatetime :" output(temp.nonReqDatetime) <br>
    "nonReqFloat :" output(temp.getNonReqFloat()) <br>
    "nonReqInt :" output(temp.getNonReqInt()) <br>
    "reqBool :" output(temp.getReqBool()) <br>
    "reqDatetime :" output(temp.reqDatetime) <br>
    "reqFloat :" output(temp.getReqFloat()) <br>
    "reqInt :" output(temp.getReqInt()) <br>
    navigate managePerson() [ ] { "Back" }
  }

  page editPerson ( temp : Person )
  {
  header
    {
    "Edit"
      }
    var
    derivedDefault
    :=
    temp.derivedDefault
    var
    derivedDefaultOption
    :=
    temp.derivedDefaultOption
    var
    derivedIntDefault
    :=
    temp.derivedIntDefault
    var
    derivedIntDefaultOption
    :=
    temp.derivedIntDefaultOption
    var
    nickname
    :=
    temp.getNickname()
    var
    nickname2
    :=
    temp.getNickname2()
    var
    nonReqBool
    :=
    temp.getNonReqBool()
    var
    nonReqDatetime
    :=
    temp.getNonReqDatetime()
    var
    nonReqFloat
    :=
    temp.getNonReqFloat()
    var
    nonReqInt
    :=
    temp.getNonReqInt()
    var
    reqBool
    :=
    temp.getReqBool()
    var
    reqDatetime
    :=
    temp.getReqDatetime()
    var
    reqFloat
    :=
    temp.getReqFloat()
    var
    reqInt
    :=
    temp.getReqInt()
    form
      {
      "derivedDefault :" input(derivedDefault) <br/>
        "derivedDefaultOption :" input(derivedDefaultOption) <br/>
        "derivedIntDefault :" input(derivedIntDefault) <br/>
        "derivedIntDefaultOption :" input(derivedIntDefaultOption) <br/>
        "nickname :" input(nickname) <br/>
        "nickname2 :" input(nickname2) <br/>
        "nonReqBool :" inputNonRequiredBool(nonReqBool) <br/>
        "nonReqDatetime :" input(nonReqDatetime) <br/>
        "nonReqFloat :" input(nonReqFloat) <br/>
        "nonReqInt :" input(nonReqInt) <br/>
        "reqBool :" input(reqBool) <br/>
        "reqDatetime :" input(reqDatetime) <br/>
        "reqFloat :" input(reqFloat) <br/>
        "reqInt :" input(reqInt) <br/>
        submit
        action
        {
          
if(derivedDefault.trim() != "") {
  temp.derivedDefault := derivedDefault;
} else {
  temp.derivedDefault := null;
}
 
if(derivedDefaultOption.trim() != "") {
  temp.derivedDefaultOption := derivedDefaultOption;
} else {
  temp.derivedDefaultOption := null;
}
 
if(derivedIntDefault != null) {
	  temp.derivedIntDefault := derivedIntDefault;
	} else {
	  temp.derivedIntDefault := null;
	}
 
if(derivedIntDefaultOption != null) {
	  temp.derivedIntDefaultOption := derivedIntDefaultOption;
	} else {
	  temp.derivedIntDefaultOption := null;
	}
 temp.nickname := nickname; temp.nickname2 := nickname2; temp.nonReqBool := nonReqBool; temp.nonReqDatetime := nonReqDatetime; temp.nonReqFloat := nonReqFloat; temp.nonReqInt := nonReqInt; temp.reqBool := reqBool; temp.reqDatetime := reqDatetime; temp.reqFloat := reqFloat; temp.reqInt := reqInt;
          temp.save();
        }
        [
        ]
        {
        "Save"
        }
        }
    navigate managePerson() [ ] { "Back" }
  }