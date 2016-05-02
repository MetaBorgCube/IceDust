module lib/icedust/newcrud-ui

section ui

  page root ( )
  {
    "New CRUD UI" <br/>
    navigate manageEntity() [] { "Manage" }
  }
  
  define main() {
    <div id="pagewrapper">
      <div id="navbar">
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
  
  define body(){
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
  
