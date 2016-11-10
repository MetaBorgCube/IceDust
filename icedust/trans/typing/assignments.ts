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

  DerivationAttribute(a, a-ty, a-mu, e)
+ DefaultAttribute   (a, a-ty, a-mu, e) :-
  where  e  : e-ty
    and  (e-ty == a-ty or e-ty <sub: a-ty) 
        else error $[Type mismatch: expected [a-ty] got [e-ty] in Derivation] on e
      
  DerivationAttribute(a, a-ty, a-mu, e)
+ DefaultAttribute   (a, a-ty, a-mu, e) :-
  where  e has multiplicity e-mu
    and (
            a-mu == ZeroOrOne() and e-mu == One()
         or a-mu == e-mu
        )
    else error $[Multiplicity mismatch: expected [a-mu] got [e-mu] in Derivation] on e

type rules // derivations well-formedness (relations)

  RelationDerived(NaBLHelp(left-ty1, left-ty2), left-name, left-mu, left-or, expr, right-mu, right-or, NaBLHelp(right-ty1, right-ty2), right-name):-
  where expr : e-ty
    and e-ty == right-ty2 else error $[Type mismatch: expected [right-ty2] got [e-ty] in Derivation] on expr

  RelationDerived(NaBLHelp(left-ty1, left-ty2), left-name, left-mu, left-or, expr, right-mu, right-or, NaBLHelp(right-ty1, right-ty2), right-name):-
  where expr has multiplicity e-mu
    and e-mu == left-mu else error $[Multiplicity mismatch: expected [left-mu] got [e-mu] in Derivation] on expr

//  RelationDerived(NaBLHelp(left-ty1, left-ty2), left-name, left-mu, left-or, expr, right-mu, right-or, NaBLHelp(right-ty1, right-ty2), right-name):-
//  where expr has ordering e-or
//    and e-or == left-or else error $[Ordering mismatch: expected [left-or] got [e-or] in Derivation] on expr

type rules // data well-formedness

  MemberValue(NaBLHelp(m, m2), val) :-
  where m   : m-ty
    and val : val-ty
    and m-ty == val-ty else error $[Type mismatch: expected [m-ty] got [val-ty] in Role Assignment] on val

  MemberValue(NaBLHelp(m, m2), val) :-
  where m has multiplicity m-mu
    and val has multiplicity val-mu
    and (
            m-mu == val-mu
         or m-mu == ZeroOrMore()
         or m-mu == ZeroOrOne() and val-mu == One()
         or m-mu == OneOrMore() and val-mu == One()
        )
    else error $[Multiplicity mismatch: expected [m-mu] got [val-mu] in Derivation] on val


