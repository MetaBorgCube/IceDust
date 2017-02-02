module typing/assignments

imports

  // constructors
  src-gen/signatures/Data-sig
  src-gen/signatures/Model-sig
  src-gen/signatures/Types-sig
  trans/api/constructors
  trans/desugaring/constructors
  
  // functions
  typing/_multiplicity-functions
  names/naming/names
  
  // // use custom runtime libraries  
 //  lib/nabl/-
 //  lib/task/-
 //  lib/types/-
 //  lib/properties/-
 //  lib/relations/-

type rules // derivations well-formedness

  DerivationAttribute(a, a-ty, a-mu, e, st)
+ DefaultAttribute   (a, a-ty, a-mu, e, st) :-
  where  e  : e-ty
    and  (e-ty == a-ty or e-ty <sub: a-ty) 
        else error $[Type mismatch: expected [a-ty] got [e-ty] in Derivation] on e
      
  DerivationAttribute(a, a-ty, a-mu, e, st)
+ DefaultAttribute   (a, a-ty, a-mu, e, st) :-
  where  e has multiplicity e-mu
    and (
            a-mu == ZeroOrOne() and e-mu == One()
         or a-mu == e-mu
        )
    else error $[Multiplicity mismatch: expected [a-mu] got [e-mu] in Derivation] on e
      
  DerivationAttribute(a, a-ty, a-mu, e, ignore)
+ DefaultAttribute   (a, a-ty, a-mu, e, ignore) :-
  where  e has strategy e-st
    and definition of a has strategy a-st
    and (
            a-st == e-st
         or a-st == OnDemandEventual()
         or e-st == Incremental()
        )
    else error $[Calculation strategy mismatch: expected [a-st] got [e-st] in Derivation] on e

type rules // derivations well-formedness (relations)

  RelationDerived(NaBLHelp(left-ty1, left-ty2), left-name, left-mu, expr, right-mu, NaBLHelp(right-ty1, right-ty2), right-name, strategy):-
  where expr : e-ty
    and e-ty == right-ty2 else error $[Type mismatch: expected [right-ty2] got [e-ty] in Derivation] on expr

  RelationDerived(NaBLHelp(left-ty1, left-ty2), left-name, left-mu, expr, right-mu, NaBLHelp(right-ty1, right-ty2), right-name, strategy):-
  where expr has multiplicity e-mu
    and e-mu == left-mu else error $[Multiplicity mismatch: expected [left-mu] got [e-mu] in Derivation] on expr
    and right-mu == ZeroOrMore() else warning $[Warning: multiplicity [right-mu] cannot be statically guaranteed.] on right-mu

type rules // data well-formedness

  MemberValue(NaBLHelp(m, m2), val) :-
  where m   : m-ty
    and val : val-ty
    and m-ty == val-ty else error $[Type mismatch: expected [m-ty] got [val-ty] in Role Assignment] on val

  MemberValue(NaBLHelp(m, m2), val) :-
  where m has multiplicity m-mu
    and val has multiplicity v-mu
    and (
            m-mu == v-mu                                               // equal is ok
         or m-mu == ZeroOrMore()                                       // definition expects most liberal multiplicity
         or v-mu == One()                                              // value provides most strict multiplicity
         or m-mu == ZeroOrMoreOrdered() and v-mu == ZeroOrOne()        // fits
         or m-mu == ZeroOrMoreOrdered() and v-mu == OneOrMoreOrdered() // fits
         or m-mu == OneOrMore()         and v-mu == OneOrMoreOrdered() // fits
        )
    else error $[Multiplicity mismatch: expected [m-mu] got [v-mu] in Derivation] on val


