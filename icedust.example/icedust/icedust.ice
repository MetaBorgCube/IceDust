module icedust

model

  entity Module {
    name : String
    desc : String = "${entities.members.desc2}"
    typeCheck : Boolean = conj(entities.typeCheck) and conj(relations.typeCheck)
  }
  
  entity Entity extends Type {
    name : String
    typeCheck : Boolean = conj(fields.typeCheck)
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
    typeCheck      : Boolean         = if(count(expression)==1) count(expression.type)==1 else true
  }
  
  relation Entity.fields * <-> 1 Field.entity_
  
  entity BidirectionalRelation {
    typeCheck : Boolean = left.typeCheck and right.typeCheck
  }
  
  relation Module.relations * <-> 1 BidirectionalRelation.module_
  
  entity Relation extends Member {
    entityName : String
    name       : String
    typeCheck  : Boolean = count(entity_)==1
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
  
  relation Module.float   ? = primitiveTypes.find(x=>x.name=="Float")   <-> PrimitiveType.asFloat
  relation Module.int     ? = primitiveTypes.find(x=>x.name=="Int")     <-> PrimitiveType.asInt
  relation Module.string  ? = primitiveTypes.find(x=>x.name=="String")  <-> PrimitiveType.asString
  relation Module.boolean ? = primitiveTypes.find(x=>x.name=="Boolean") <-> PrimitiveType.asBoolean
  
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
    type2 : Type? = if((left.type == module_.float and right.type == module_.float <+ false)) module_.boolean (inline)
  }
  relation Gte.left  1 <-> ? Expression.gteLeft
  relation Gte.right 1 <-> ? Expression.gteRight
  
  entity Avg extends Expression {
    type2 : Type? = if((child.type == module_.float <+ false)) module_.float (inline)
  }
  relation Avg.child  1 <-> ? Expression.avg_
  
  entity Conj extends Expression {
    type2 : Type? = if((child.type == module_.boolean <+ false)) module_.boolean (inline)
  }
  relation Conj.child  1 <-> ? Expression.conj_
  
  entity If extends Expression {
    type2 : Type? = if((if_.type == module_.boolean and then_.type == else_.type <+ false)) then_.type (inline)
  }
  relation If.if_  1 <-> ? Expression.if_2
  relation If.then_ 1 <-> ? Expression.then_2
  relation If.else_ 1 <-> ? Expression.else_2
  
  entity Ref extends Expression {
    name  : String
    type2 : Type? = member.type (inline)
  }
  
  entity MemberAccess extends Expression {
    name  : String
    type2 : Type? = member.type (inline)
  }
  relation MemberAccess.child  1 <-> ? Expression.memberAccess
  
  relation Expression.parent ? =
    gteLeft <+
    gteRight <+
    avg_ <+
    conj_ <+
    if_2 <+
    then_2 <+
    else_2 <+
    memberAccess
    <-> Expression.children
  
  relation Field.expression ? <-> ? Expression.field
  
  relation Expression.context ? =
    field.entity_ <+
    parent.context
    <-> * Entity.expressions
    
  relation Ref.member ? =
    context.members.find(x=>x.name == name)
    <-> * Member.refs
    
  relation MemberAccess.member ? =
    child.type.filter(:Entity).members.find(x=>x.name == name)
    <-> * Member.refs2
  
  relation Expression.type ? =
    this.filter(:Ref).type2 <+
    (this.filter(:LitFloat).type2) <+
    (this.filter(:Gte).type2) <+
    (this.filter(:Avg).type2) <+
    (this.filter(:Conj).type2) <+
    (this.filter(:If).type2) <+
    (this.filter(:MemberAccess).type2)
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
          {
            name="grade"
            typeName="Float"
            expression=:If{
              if_  =:Conj{child=:MemberAccess{child=:Ref{name="children"} name="pass"}}
              then_=:Avg {child=:MemberAccess{child=:Ref{name="children"} name="grade"}}
              else_=:LitFloat{value=1.0}
            }
          }
      },
      {
        name="Assignment"
        fields=
          {
            name="avgGrade"
            typeName="Float"
            expression=:Avg{child=:MemberAccess{child=:Ref{name="submissions"} name="grade"}}
          }
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
      },
      {
        left ={entityName="Submission" name="parent"}
        right={entityName="Submission" name="children"} 
      }
    primitiveTypes=
      {name="String"},
      {name="Int"},
      {name="Float"},
      {name="Boolean"}
  }

execute

  mod.typeCheck
  mod.desc
