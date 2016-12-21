  module test
  model
  entity Node{}
//  relation Node.maybe ? <-> 1 Node.one {}
//  relation Node.star * <-> + Node.plus {}
  relation NodeMaybeRelation {
    Node.maybeRelation ? -> one
    Node.oneRelation 1 -> maybe
    maybe.one <-> one.maybe
  }

  relation NodeStarRelation {
    Node.starRelation * -> plus
    Node.plusRelation + (ordered) -> star
    star.plus <-> plus.star
  }
  data
  n : Node {
    maybe = <e : NodeMaybeRelation { } > n
    star  = <e2 : NodeStarRelation { } > n
  } 
  execute 
  3
  n.maybeRelation.maybe