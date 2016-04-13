module library

// library modeled after the Booster2 example on https://github.com/Booster2/Booster2/blob/master/Booster2/test/library2.boo2

model

  // represents one physical copy of a book
  entity Book {
    title : String
  }
  
  // represents a person borrowing books from the library
  entity Reader {
    name        : String
    borrowCount : Int = count(borrowed)
    subsCount   : Int = count(subs)
  }
  
  // represents a person owning books in the library
  entity Lender {
    maximum         : Int
    holdCount       : Int = count(holdings)
    memberCount     : Int = count(members)
    memberInvariant : Boolean = memberCount <= maximum
  }
  
  // books can be borrowed from the library
  relation Book.borrower ? <-> * Reader.borrowed
  
  // all books in the library are owned by someone
  relation Book.owner 1 <-> * Lender.holdings
  
  // people borrowing books can subscribe themselves to people owning books
  relation Reader.subs * <-> * Lender.members

data

  alice : Lender {
    maximum = 2
    holdings =
      theLordOfTheRings1 {
        title = "The Lord of The Rings"
      },
      theLordOfTheRings2 {
        title = "The Lord of The Rings"
      },
      theLordOfTheRings3 {
        title = "The Lord of The Rings"
      }
  }
  bob : Lender {
    maximum = 3
    holdings =
      theLionTheWitchAndTheWardrobe1 {
        title = "The Lion, the Witch and the Wardrobe"
      },
      theLionTheWitchAndTheWardrobe2 {
        title = "The Lion, the Witch and the Wardrobe"
      }
  }
  
  charles : Reader {
    name = "Charles"
    borrowed =
      theLordOfTheRings2,
      theLionTheWitchAndTheWardrobe1
    subs =
      alice,
      bob
  }
  dave : Reader {
    name = "Dave"
    borrowed =
      theLordOfTheRings1
  }

execute

  "How many books did " + charles.name + " borrow?"
  charles.borrowCount
  
  "Is the number of Lender subscribers below their maximums?"
  (alice ++ bob).memberInvariant
