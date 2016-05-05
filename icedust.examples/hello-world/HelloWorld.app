application HelloWorld

imports lib/icedust/newcrud-ui

imports lib/icedust/Expressions

section  data

  init
  {
    var hello := Message{} ;
    hello.text := "Hello World!";
    hello.save();
  }

section  model

  entity Envelope {
    text : String ( default= null )
    function getText ( ) : String
    {
      return this.text;
    }
    static function getText ( en : Envelope ) : String
    {
      return if ( en == null ) ( null as String ) else en.getText();
    }
    static function getText ( entities : List<Envelope> ) : List<String>
    {
      return [ en.getText() | en : Envelope in entities where en.getText() != null ];
    }
  }

  entity Message {
    text : String ( default= null )
    function getText ( ) : String
    {
      return this.text;
    }
    static function getText ( en : Message ) : String
    {
      return if ( en == null ) ( null as String ) else en.getText();
    }
    static function getText ( entities : List<Message> ) : List<String>
    {
      return [ en.getText() | en : Message in entities where en.getText() != null ];
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
    navigate manageEnvelope() [ ] { "Envelope" }
      }

  navbaritem
    {
    navigate manageMessage() [ ] { "Message" }
      }

  }

  page manageEnvelope ( )
  {
  navigate createEnvelope() [ ] { "Create" }
    <
    br
    />
    for
    (
    entity
    :
    Envelope
    )
    {
    output ( entity.name )
    navigate envelope(entity) [ ] { "View" }
    " "
    navigate editEnvelope(entity) [ ] { "Edit" }
    " "
    submit
    (
    "Remove"
    ,
    removeEnvelope(entity)
    )
    [
    ]
    <
    br
    />
    }
    action removeEnvelope ( entity : Envelope )
    {
      entity.delete();
    }
  }

  page createEnvelope ( )
  {
  var temp := Envelope{}
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
        derive editRows from temp for ( text )
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
      return manageEnvelope();
    }
  }

  page envelope ( arg : Envelope )
  {
  }

  page editEnvelope ( arg : Envelope )
  {
  }

  page manageMessage ( )
  {
  navigate createMessage() [ ] { "Create" }
    <
    br
    />
    for
    (
    entity
    :
    Message
    )
    {
    output ( entity.name )
    navigate message(entity) [ ] { "View" }
    " "
    navigate editMessage(entity) [ ] { "Edit" }
    " "
    submit
    (
    "Remove"
    ,
    removeMessage(entity)
    )
    [
    ]
    <
    br
    />
    }
    action removeMessage ( entity : Message )
    {
      entity.delete();
    }
  }

  page createMessage ( )
  {
  var temp := Message{}
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
        derive editRows from temp for ( text )
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
      return manageMessage();
    }
  }

  page message ( arg : Message )
  {
  }

  page editMessage ( arg : Message )
  {
  }