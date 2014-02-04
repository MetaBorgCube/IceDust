import java.util.Collection;
import java.util.HashSet;

class example  
{ 
  public static void main(String[] args)
  { 
    User me = new User();
    Post p1 = new Post();
    p1.set_title("First post");
    Post p2 = new Post();
    p2.set_title("Second post");
    p2.set_body("Some text");
    UserPost up1 = new UserPost();
    up1.User = me;
    me.UserPost_User.add(up1);
    up1.Post = p1;
    p1.UserPost_Post.add(up1);
    UserPost up2 = new UserPost();
    up2.User = me;
    me.UserPost_User.add(up2);
    up2.Post = p2;
    p2.UserPost_Post.add(up2);
    System.out.println(me.UserPost_User.size());
  }
}

class User  
{ 
  public User(){
	  UserPost_User = new HashSet<UserPost>();
  }
  
  private String name;

  public String get_name()
  { 
    return "my name";
  }
  
  public Collection<UserPost> UserPost_User;
}

class Post  
{ 
	public Post(){
	  UserPost_Post = new HashSet<UserPost>();
  }
	
  private String title;

  public void set_title(String title)
  { 
    this.title = title;
  }

  public String get_title()
  { 
    return title;
  }

  private String body;

  public void set_body(String body)
  { 
    this.body = body;
  }

  public String get_body()
  { 
    return body != null ? body : get_title();
  }
  
  public Collection<UserPost> UserPost_Post;
}

class UserPost  
{ 
  public User User;

  public Post Post;
}