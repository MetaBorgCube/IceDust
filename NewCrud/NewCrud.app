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
    fullname : String ( default= null )
    function getFullname ( ) : String
    {
      return if ( this.fullname != null ) this.fullname else this.calculateFullname();
    }
    static function getFullname ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getFullname();
    }
    static function getFullname ( entities : List<Person> ) : List<String>
    {
      return [ en.getFullname() | en : Person in entities where en.getFullname() != null ];
    }
    function calculateFullname ( ) : String
    {
      return Expressions.plus_String(Expressions.plus_String(Person.getName(this), " "), ( Expressions.choice_One_One(Person.getNickname(this), "") as String ));
    }
    name : String ( validate(name != null && name.trim() != "", "Name cannot be empty!") )
    function getName ( ) : String
    {
      return this.name;
    }
    static function getName ( en : Person ) : String
    {
      return if ( en == null ) ( null as String ) else en.getName();
    }
    static function getName ( entities : List<Person> ) : List<String>
    {
      return [ en.getName() | en : Person in entities where en.getName() != null ];
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
    nonReqInt : Int ( default = null )
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
    reqBool : Bool ( validate(reqBool != null, "reqBool cannot be empty!") )
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
    reqDatetime : DateTime ( validate(reqDatetime != null, "reqDatetime cannot be empty!") )
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
    reqFloat : Float ( validate(reqFloat != null, "reqFloat cannot be empty!") )
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
    reqInt : Int ( validate(reqInt != null, "reqInt cannot be empty!")  )
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
  
section applicationmenu

  define applicationmenu() {
  	navbaritem {
  	  navigate managePerson() [] { "Manage Persons" }
  	}
  }

section pagesForPerson

  page managePerson() {
  	applicationmenu() <br/>
  	"Manage Persons:" <br/>
  	navigate createPerson() [] { "Create" }
  	<br/>
  	for(p: Person) {
  	  output(p.getName())
  	  navigate viewPerson(p) [] { "View" }
  	  " "
  	  navigate editPerson(p) [] { "Edit" }
  	  " "
  	  action("Remove", removeEntity(p))
  	  <br/>
  	}
  	navigate root() [] { "Back" }
  	
  	action removeEntity(p: Person) {
  	  p.delete();
  	}
  }
  
  page createPerson() {
  	applicationmenu() <br/>
  	var name : String
  	var nickname : String
  	var reqInt : Int
  	var nonReqInt : Int
  	var reqFloat : Float
  	var nonReqFloat : Float
  	var reqBool : Bool
  	var nonReqBool : Bool
  	var reqDatetime : DateTime
  	var nonReqDatetime : DateTime
  	"Create Person:" <br/>
  	form {
      "Name: " input(name) <br/>
      "Nickname: " input(nickname) <br/>
      "reqInt: " input(reqInt) <br/>
      "nonReqInt: " input(nonReqInt) <br/>
      "reqFloat: " input(reqFloat) <br/>
      "nonReqFloat: " input(nonReqFloat) <br/>
      "reqBool: " input(reqBool) <br/>
      "nonReqBool: " inputNonRequiredBool(nonReqBool) <br/>
      "reqDatetime: " input(reqDatetime) <br/>
      "nonReqDatetime: " input(nonReqDatetime) <br/>
      submit action {
      	var p := Person {
  	  	  name := name,
  	  	  nickname := nickname,
  	  	  reqInt := reqInt,
  	  	  nonReqInt := nonReqInt,
  	  	  reqFloat := reqFloat,
  	  	  nonReqFloat := nonReqFloat,
  	  	  reqBool := reqBool,
  	  	  nonReqBool := nonReqBool,
  	  	  reqDatetime := reqDatetime,
  	  	  nonReqDatetime := nonReqDatetime
	  	};
	  	p.save();
      } { "Save" }
  	}
  	<br/>
  	navigate managePerson() [] { "Back" }
  }
  
  page viewPerson(p: Person) {
  	applicationmenu() <br/>
  	"View Person:" <br/>
  	"Name: " output(p.getName()) <br/>
  	"Nickname: " output(p.getNickname()) <br/>
  	"Full name: " output(p.getFullname()) <br/>
  	"reqInt: " output(p.getReqInt()) <br/>
  	"nonReqInt: " output(p.getNonReqInt()) <br/>
  	"reqFloat: " output(p.getReqFloat()) <br/>
  	"nonReqFloat: " output(p.getNonReqFloat()) <br/>
  	"reqBool: " output(p.getReqBool()) <br/>
  	"nonReqBool: " output(p.getNonReqBool()) <br/>
  	"reqDatetime: " output(p.reqDatetime) <br/>
  	"nonReqDatetime: " output(p.nonReqDatetime) <br/>
  	navigate managePerson() [] { "Back" }
  }
  
  page editPerson(p: Person) {
  	applicationmenu() <br/>
  	"Edit Person:" <br/>
  	var name := p.getName()
  	var nickname := p.getNickname()
  	var reqInt := p.getReqInt()
  	var nonReqInt := p.getNonReqInt()
  	var reqFloat := p.getReqFloat()
  	var nonReqFloat := p.getNonReqFloat()
  	var reqBool := p.getReqBool()
  	var nonReqBool := p.getNonReqBool()
  	var reqDatetime := p.getReqDatetime()
  	var nonReqDatetime := p.getNonReqDatetime()
  	form {
  	  "Name: " input(name) <br/>
  	  "Nickname: " input(nickname) <br/>
  	  "Full name:" output(p.getFullname()) <br/>
  	  "reqInt: " input(reqInt) <br/>
      "nonReqInt: " input(nonReqInt) <br/>
      "reqFloat: " input(reqFloat) <br/>
      "nonReqFloat: " input(nonReqFloat) <br/>
      "reqBool: " input(reqBool) <br/>
      "nonReqBool: " inputNonRequiredBool(nonReqBool) <br/>
      "reqDatetime: " input(reqDatetime) <br/>
      "nonReqDatetime: " input(nonReqDatetime) <br/>
  	  submit action {
  	  	p.name := name;
  	    p.nickname := nickname;
  	    p.reqInt := reqInt;
  	    p.nonReqInt := nonReqInt;
  	    p.reqFloat := reqFloat;
  	    p.nonReqFloat := nonReqFloat;
  	    p.reqBool := reqBool;
  	    p.nonReqBool := nonReqBool;
  	    p.reqDatetime := reqDatetime;
  	    p.nonReqDatetime := nonReqDatetime;
  	    p.save();
  	  } { "Save" }
  	}
  	navigate managePerson() [] { "Back" }
  }
  