module blog // >>> Solving constraints <<< Finished in 2.11s

model

  entity User {
    name : String  = "my name" 
  }

  entity Post {
    title : String  
    body : String  = title (default)
  }

  relation Post.author 1 <-> * User.posts

data

  me : User {
    posts =
      p1 {title = "First post"},
      p2 {title = "Second post" body = "Some text"}
  }

execute

  me.posts // give Posts that are authored by me

  me.posts.title // my blogpost titles
