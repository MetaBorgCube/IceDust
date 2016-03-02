module recursiveavg

model

  entity Node {
    value : Int ? = avg ( this.children.value ) (default)
  }

  relation Node.parent ? <-> * Node.children


data

  root : Node {
    children = 
      n1 {
        children = 
          n11 {value = 1},
          n12 {value = 3}
      },
      n2 {value=4}
  }

execute

  n1.value // we defined this as 2

  n2.value // we defined this as 4

  root.value // the average of this is 3