module HelloWorld

model

  entity Message {
    text : String  
  }
  entity Envelope {
    text: String
  }
  
data

  hello : Message {
    text = "Hello World!"
  }

execute

  hello . text
