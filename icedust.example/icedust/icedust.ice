module icedust

model

  entity Module {
    name : String
    desc : String = "${entities.members.desc2}"
  }
  
  entity Entity extends Type {
    name : String
  }
  
  relation Module.entities * <-> 1 Entity.module_
  
  entity Member {
    name : String  (abstract)
    desc : String = "${entity_2.name}.${name} : ${type.name}${if(count(expression2)==1) " (expr = ${expression2.desc})"}"
    desc2: String = desc + "\n" (inline)
    expression2 : Expression? = this.filter(:Field).expression (inline)
  }
  
  entity Field extends Member {
    name     : String
    typeName : String
    module_        : Module 1        = entity_.module_ (inline)
    primitiveTypes : PrimitiveType * = module_.primitiveTypes (inline)
  }
  
  relation Entity.fields * <-> 1 Field.entity_
  
  entity BidirectionalRelation { }
  
  relation Module.relations * <-> 1 BidirectionalRelation.module_
  
  entity Relation extends Member {
    entityName : String
    name       : String
  }
  
  relation BidirectionalRelation.left  1 <-> ? Relation.asLeft
  relation BidirectionalRelation.right 1 <-> ? Relation.asRight
  
  relation BidirectionalRelation.sides * = left ++ right <-> 1 Relation.bidir
  
  relation Relation.inverse2 ? = asLeft.right <+ asRight.left <-> 1 Relation.inverse
  
  relation Relation.entity_ ? = bidir.module_.entities.find(x=>x.name==entityName) <-> * Entity.relations
  
  relation Entity.members = fields ++ relations <-> Member.entity_2
  
  entity Type {
    name : String
  }
  
  entity PrimitiveType extends Type { }
  
  relation Module.primitiveTypes * <-> 1 PrimitiveType.module_
  
  relation Module.float ? = primitiveTypes.find(x=>x.name=="float") <-> PrimitiveType.asFloat
  
  relation Field.primitiveType ? = primitiveTypes.find(t=>t.name == typeName) <-> * PrimitiveType.fields
  
  relation Member.type ? =
    this.filter(:Field).primitiveType <+
    (this.filter(:Relation).inverse.entity_)
    <-> Type.members2
  
  entity Expression {
    module_ : Module? = context.module_ (inline)
    desc    : String  = "(${children.desc} : ${type.name})"
  }
  
  entity LitFloat extends Expression {
    value : Float
    type2 : Type? = module_.float (inline)
  }
  
  entity Gte extends Expression {
    type2 : Type? = if((left.type == module_.float and right.type == module_.float <+ false)) module_.float (inline)
  }
  
  relation Gte.left  1 <-> ? Expression.gteLeft
  relation Gte.right 1 <-> ? Expression.gteRight
  
  entity Ref extends Expression {
    name  : String
    type2 : Type? = member.type (inline)
  }
  
  relation Expression.parent ? =
    gteLeft <+
    gteRight
    <-> Expression.children
  
  relation Field.expression ? <-> ? Expression.field
  
  relation Expression.context ? =
    field.entity_ <+
    parent.context
    <-> * Entity.expressions
    
  relation Ref.member ? =
    context.members.find(x=>x.name == name)
    <-> * Member.refs
  
  relation Expression.type ? =
    this.filter(:Ref).type2 <+
    (this.filter(:LitFloat).type2) <+
    (this.filter(:Gte).type2)
    <-> * Type.expressions2

data

  mod:Module{
    name="weblabMicro"
    entities=
      {
        name="Student"
        fields=
          {name="name" typeName="String"}
      },
      {
        name="Submission"
        fields=
          {name="pass"  typeName="Boolean" expression=:Gte{left=:Ref{name="grade"} right=:LitFloat{value=5.5}}},
          {name="grade" typeName="Float"}
      },
      {
        name="Assignment"
        fields=
          {name="avgGrade" typeName="Float"}
      }
    relations=
      {
        left ={entityName="Student"    name="submissions"}
        right={entityName="Submission" name="student"} 
      },
      {
        left ={entityName="Assignment" name="submissions"}
        right={entityName="Submission" name="assignment"} 
      },
      {
        left ={entityName="Assignment" name="parent"}
        right={entityName="Assignment" name="children"} 
      }
    primitiveTypes=
      {name="String"},
      {name="Int"},
      {name="Float"},
      {name="Boolean"}
  }

execute

  mod.desc
  