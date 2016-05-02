application NewCrud

imports lib/icedust/newcrud-ui

imports lib/icedust/Expressions

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
    name : String ( validate(name != null && name.trim() != "", "Name cannot be empty") )
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
  }
  
  entity PersonList {
  	persons -> List<Person>
  }
  
  var globalList := PersonList { }

section pages

  page manageEntity() {
  	"Manage Persons:" <br/>
  	navigate createEntity() [] { "Create" }
  	<br/>
  	for(p: Person in globalList.persons) {
  	  output(p.getName())
  	  navigate viewEntity(p) [] { "View" }
  	  " "
  	  navigate editEntity(p) [] { "Edit" }
  	  " "
  	  action("Remove", removeEntity(p))
  	  <br/>
  	}
  	
  	action removeEntity(p: Person) {
  	  globalList.persons.remove(p);
  	  globalList.save();
  	}
  }
  
  page createEntity() {
  	var name : String
  	var nickname : String
  	"Create Person:" <br/>
  	form {
      "Name: " input(name) <br/>
      "Nickname: " input(nickname) <br/>
      submit("Save", createPerson(name, nickname))
  	}
  	<br/>
  	navigate manageEntity() [] { "Back" }
  	
  	action createPerson(newname : String, newnickname : String) {
  	  var p := Person {
  	  	name := newname,
  	  	nickname := newnickname
  	  };
  	  globalList.persons.add(p);
  	  p.save();
  	  globalList.save();
  	}
  }
  
  page viewEntity(p: Person) {
  	"View Person:" <br/>
  	"Name: " output(p.getName()) <br/>
  	"Nickname: " output(p.getNickname()) <br/>
  	"Full name: " output(p.getFullname()) <br/>
  	navigate manageEntity() [] { "Back" }
  }
  
  page editEntity(p: Person) {
  	"View Person:" <br/>
  	var name := p.name
  	var nickname := p.nickname
  	form {
  	  "Name: " input(name) <br/>
  	  "Nickname: " input(nickname) <br/>
  	  submit("Save", editPerson(p, name, nickname))
  	}
  	navigate manageEntity() [] { "Back" }
  	
  	action editPerson(cperson: Person, newname : String, newnickname : String) {
  	  cperson.name := newname;
  	  cperson.nickname := newnickname;
  	  cperson.save();
  	}
  }
  