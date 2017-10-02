module scopegraph

model

  entity Scope{
    id : Int
    
    // non transitive imports D < I < P
    definitions_            : Definition* = definitions                                                                                     (inline)
    importedNamesAll        : Definition* = imports.definition.associatedScope.definitions                                                  (inline)
    importedNamesVisible    : Definition* = importedNamesAll.filter(x => count(definitions_.filter(y => y.name == x.name))==0)              (inline)
    nonParentVisisbleNames  : Definition* = definitions_ ++ importedNamesVisible                                                            (inline)
    parentVisibleNames      : Definition* = parent.visibleNames.filter(x => count(nonParentVisisbleNames.filter(y => y.name == x.name))==0) (inline)
    visibleNames_           : Definition* = nonParentVisisbleNames ++ parentVisibleNames                                                    (inline)
    
    allReferencesResolved             : Boolean = conj(references.isResolved ++ imports.isResolved)
    allReferencedResolvedTransivitive : Boolean = allReferencesResolved and conj(children.allReferencedResolvedTransivitive)
    
    description : String = "${references.description}${children.description}" 
  }
  
  entity Name{
    name : String
    id   : Int
    description_ : String = "${name}${id}"
  }
  
  entity Definition extends Name {
    numUses : Int = count(uses)
  }
  
  entity Reference extends Name {
    isResolved : Boolean = count(definition)==1
    description: String  = "${description_} resolves to ${definition.description_}\n"
  }
  
  entity Import extends Name {
    isResolved : Boolean = count(definition)==1
  }
  
  relation Scope.parent ? <-> * Scope.children
  
  relation Definition.scope 1 <-> * Scope.definitions
  
  relation Reference.scope 1  <-> * Scope.references

  relation Import.scope 1 <-> * Scope.imports
  
  relation Definition.associatedScope ? <-> ? Scope.associatedName
  
  relation Scope.visibleNames = visibleNames_ <-> Definition.visibleIn
  
  relation Reference.definition ? = scope.visibleNames.find(x => x.name == name) <-> Definition.uses
  
  relation Import.definition ? = scope.visibleNames.find(x => x.name == name) <-> Definition.imports
    
data

// Fig 7 from scopegraph paper (but non-transitive imports!)
//
//  def c1 = 4
//  module A2 {
//   import B3
//   def a4 = b5 + c6 //b5 should resolve to b9 (definition in imported), c6 should resolve to c1 as there is no local definition or import
//  }
//  module B7 {
//   import C8
//   def b9 = 0
//  }
//  module C10 {
//   def b11 = 1
//   def c12 = b13 //b13 should resolve to b11 (definition in same scope)
//  }

  globalScope:Scope{
    id=1
    definitions=
      {name="c" id=1},
      {name="A" id=2 associatedScope=scope2},
      {name="B" id=7 associatedScope=scope3},
      {name="C" id=10 associatedScope=scope4}
    children=
      scope2{
        id=2
        imports=
          {name="B" id=3} 
        definitions=
          {name="a" id=4}
        references=
          {name="b" id=5},
          {name="c" id=6}
      },
      scope3{
        id=3
        imports=
          {name="C" id=8}
        definitions=
          {name="b" id=9}
      },
      scope4{
        id=4
        definitions=
          {name="b" id=11},
          {name="c" id=12}
        references=
          {name="b" id=13}
      }
  }
  
execute

  "all references resolved: ${globalScope.allReferencedResolvedTransivitive}"
  //all references resolved: true

  globalScope.description
  //b5 resolves to b9
  //c6 resolves to c1
  //b13 resolves to b11
  