module cms

model

  trait File {
  }
  
  entity Image {
    path        : String
    inUse       : Boolean = count(usedBy)>0
    usedByNames : String  = concat(usedBy.name)
    display     : String  = "<img src='" + path + "'>"
  }
  
  trait HasImage {
    name : String
  }
  
  relation HasImage.image ? <-> * Image.usedBy
  
  entity Page extends HasImage, Displayable {
    title   : String
    body    : String
    display : String = menu + breadcrumbs + "<h1>" + title + "</h1>" + body + (image.display<+"") + "Authors: " + concat(editedBy.name)
    url     : String = title
    name    : String = title
  }
  
  entity Profile extends Displayable{
    name     : String = user.name
    bio      : String
    display  : String = menu + breadcrumbs + "<h1>" + name + "</h1>" + "bio:" + bio + (user.image.display<+"")
    url      : String = "profile/"+name
  }
  
  trait Displayable {
    display     : String
    url         : String
    label       : String
    link        : String  = "<a href='" + url + "'>" + label + "</a>"
    breadcrumbs : String  = parent.breadcrumbs + " > " + parent.link <+ ""
    menu        : String  = concat(children.link)
  }
  
  relation Displayable.children * <-> ? Displayable.parent
  
  entity User extends HasImage {
    name : String
  }
  
  relation User ? <-> 1 Profile
  
  relation User * <-> * Page.editedBy
