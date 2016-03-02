module lib/relations/crud-ui

section ui

  page root ( )
  {
    main()
    define body() {
      "Hello world!"
    }
  }
  
  define override main() {
    <div id="pagewrapper">
      <div id="navbar">
        applicationmenu()
      </div>
      <div id="content">
        body()
      </div>
      <div id="clear"></div>
      <div id="push"></div>
    </div>
    <div id="footer">
      <span id="footercontent">"powered by " <a href="http://webdsl.org">"WebDSL"</a></span>
    </div>
  }
  
  define override body(){
    "default body"
  }
  
  define mainheader() {
    navigate(root()){
      image("/images/logosmall.png")
    }
  }
  
  define navbaritem(){
    <span class="navbaritem">
      elements()
    </span>
  }
   
  define override errorTemplateInput(messages : List<String>){
    elements()
    for(ve: String in messages){
      <tr style = "color: #FF0000;border: 1px solid #FF0000;">
        <td></td>
        <td> 
          output(ve)
        </td>
      </tr>
    }
  }
  