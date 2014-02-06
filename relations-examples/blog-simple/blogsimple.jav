import java.util.Collection;
import java.util.HashSet;

class blogsimple  
{ 
  public static void main(String[] args)
  { 
    User me = new User();
    Post first = new Post();
    Post second = new Post();
    UserPost p1 = new UserPost();
    p1.User = me;
    me.UserPost_User.add(p1);
    p1.Post = first;
    first.UserPost_Post.add(p1);
    UserPost p2 = new UserPost();
    p2.User = me;
    me.UserPost_User.add(p2);
    p2.Post = second;
    second.UserPost_Post.add(p2);
    System.out.println(UserPost.Post_out(UserPost.User_in(toCollection(me))));
  }
  
  public static <E> Collection<E> toCollection(E e){
		Collection<E> collection = new HashSet<E>();
		collection.add(e);
		return collection;
	}
}

class User  
{ 
  public User () 
  { 
    UserPost_User = new HashSet<UserPost>();
  }

  public Collection<UserPost> UserPost_User;
}

class Post  
{ 
  public Post () 
  { 
    UserPost_Post = new HashSet<UserPost>();
  }

  public Collection<UserPost> UserPost_Post;
}

class UserPost  
{ 
  public UserPost () 
  { }

  public User User;

  public Post Post;
  
  public static Collection<UserPost> User_in(Collection<User> in){
	  Collection<UserPost> result = new HashSet<UserPost>();
	  for(User elem : in){
		  result.addAll(elem.UserPost_User);
	  }
	  return result;
  }
  
  public static Collection<User> User_out(Collection<UserPost> out){
	  Collection<User> result = new HashSet<User>();
	  for(UserPost u : out){
		  result.add(u.User);
	  }
	  return result;
  }
  
  public static Collection<UserPost> Post_in(Collection<Post> in){
	  Collection<UserPost> result = new HashSet<UserPost>();
	  for(Post elem : in){
		  result.addAll(elem.UserPost_Post);
	  }
	  return result;
  }
  
  public static Collection<Post> Post_out(Collection<UserPost> out){
	  Collection<Post> result = new HashSet<Post>();
	  for(UserPost u : out){
		  result.add(u.Post);
	  }
	  return result;
  }
}