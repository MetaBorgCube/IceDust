(*
Proof of type- and multiplicity soundness for IceDust expressions.

Proofs:
- type preservation: values are of the correct type.
- termination/totality: if an expression has a type, it evaluates.
- multiplicity preservation: evaluation yields the right amount of values.

Portion of the IceDust language:
- all expressions without:
  - filter, find, and orderBy (no environments)
  - objects (no store)

This a self-contained file containing:
- some higher order helper functions
- interpreter native functions
- signatures of ast, values, types, and multiplicities
- interpreter
  - as relation
  - as function
  - proof of equality
  - examples
- type checker
  - relation
  - function
  - proof of equality
  - example
- multiplicity checker
  - relation
  - function
  - proof of equality
  - examples
- auxiliary functions for type- and multiplicity soundness
  - type of value
  - value contained in multiplicity
    - relation
    - function
    - proof of equality
- type preservation proof
  - by induction over evaluation relation
- type completeness proof: all expressions that have a type, evaluate to a value
  - by induction over typing function
- multiplicity preservation proof
  - a list of helper lemmas for a groups of operations that behave
    differently with respect to multiplicities
  - main proof by induction over evaluation relation
*)

Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.

(***** higher order helper functions *****)
Fixpoint list_pair_with {X Y : Type} (lx : list X) (y : Y) : list (X*Y) :=
  match lx with
  | [] => []
  | x :: tx => (x, y) :: (list_pair_with tx y)
  end.

Fixpoint list_pair_with2 {X Y : Type} (x : X) (ly : list Y) : list (X*Y) :=
  match ly with
  | [] => []
  | y :: ty => (x, y) :: (list_pair_with2 x ty)
  end.

Fixpoint list_crossproduct {X Y : Type}
  (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx with
  | [] => []
  | x :: tx => (list_pair_with2 x ly) ++ (list_crossproduct tx ly)
  end.

Fixpoint fmap {A B:Type} (f:A -> option B) (l:list A) : list B :=
  match l with
    | nil => nil
    | cons x t => 
        match f x with
        | None   =>      (fmap f t)
        | Some y => y :: (fmap f t)
        end
  end.

Fixpoint foldo {A:Type} (f:A->A->A) (l:list A) : option A :=
  match l with
  | []     => None
  | h :: t => Some(fold_left f t h)
  end.

Function to_list {X:Type} (v : option X) : list X :=
  match v with
  | None => []
  | Some x => [x]
  end.

Function funtuple {X Y Z : Type} (f: X -> Y -> Z) (t:X*Y) : Z :=
  match t with
  | (v1, v2) => f v1 v2
  end.

Function iftuple {X : Type} (t : (bool*(X*X))) : X :=
  match t with
  | (true,  (v2, _ )) => v2
  | (false, (_ , v3)) => v3
  end.

(***** interpreter native functions *****)
Function gtb  (n1 n2 : nat)  : bool := negb (leb n1 n2).
Function geb  (n1 n2 : nat)  : bool := negb (ltb n1 n2).
Function neqb (n1 n2 : nat)  : bool := negb (eqb n1 n2).
Function beq  (b1 b2 : bool) : bool := (Coq.Bool.Bool.eqb b1 b2).
Function bneq (b1 b2 : bool) : bool := negb (beq b1 b2).
Function divo (n1 n2 : nat)  : option nat :=
  match n2 with
  | 0 => None
  | _ => Some (div n1 n2)
  end.
Function moduloo (n1 n2 : nat) : option nat :=
  match n2 with
  | 0 => None
  | _ => Some (modulo n1 n2)
  end.
Function choice {X:Type} (l1 l2 : list X) : list X :=
  match l1 with
  | h :: t => l1
  | []     => l2
  end.
Function maxo(l : list nat) : option nat := foldo max l.
Function mino(l : list nat) : option nat := foldo min l.
Function sum (l : list nat) : nat        := fold_left plus l 0.
Function avgo(l : list nat) : option nat :=
  match (length l) with
  | 0 => None
  | n => Some((sum l) / n)
  end.
Function conj(l : list bool) : bool := fold_left andb l true.
Function disj(l : list bool) : bool := fold_left orb  l false.

Fixpoint indexOf_nat (l : list nat) (x : nat) : option nat :=
  match l with
  | []     => None
  | h :: t =>
      match eqb x h with
      | true  => Some 0
      | false =>
          match indexOf_nat t x with
          | None   => None
          | Some i => Some (i+1)
          end
      end
  end.
Fixpoint indexOf_bool (l : list bool) (x : bool) : option nat :=
  match l with
  | []     => None
  | h :: t =>
      match beq x h with
      | true  => Some 0
      | false =>
          match indexOf_bool t x with
          | None   => None
          | Some i => Some (i+1)
          end
      end
  end.

(***** signatures *****)
Inductive expr : Type :=
  | EInt      : nat -> expr
  | ETrue     : expr
  | EFalse    : expr
  | ENullInt  : expr
  | ENullBool : expr
  | ENot      : expr -> expr
  | EMax      : expr -> expr
  | EMin      : expr -> expr
  | ESum      : expr -> expr
  | EAvg      : expr -> expr
  | EConj     : expr -> expr
  | EDisj     : expr -> expr
  | ECount    : expr -> expr
  | EAnd      : expr -> expr -> expr
  | EOr       : expr -> expr -> expr
  | EPlus     : expr -> expr -> expr
  | EMinus    : expr -> expr -> expr
  | EMult     : expr -> expr -> expr
  | EDiv      : expr -> expr -> expr
  | EModulo   : expr -> expr -> expr
  | EEq       : expr -> expr -> expr
  | ENeq      : expr -> expr -> expr
  | ELt       : expr -> expr -> expr
  | ELte      : expr -> expr -> expr
  | EGt       : expr -> expr -> expr
  | EGte      : expr -> expr -> expr
  | EIf       : expr -> expr -> expr -> expr
  | EConcat   : expr -> expr -> expr
  | EChoice   : expr -> expr -> expr
  | EFirst    : expr -> expr
  | EElemAt   : expr -> expr -> expr
  | EIndexOf  : expr -> expr -> expr.

Inductive type : Type :=
  | intty  : type
  | boolty : type.

Inductive mult : Type :=
  | one : mult
  | zeroOrOne : mult
  | oneOrMore : mult
  | zeroOrMore : mult.

Inductive val : Type :=
  | intv  : list nat -> val
  | boolv : list bool -> val.

(***** interpreter *****

Note that the IceDust language does not feature shortcut evaluation
as the incremental runtime of IceDust (which is not modeled in this file)
does bottom up evaluation. *)

Reserved Notation "e '\\' v"
                  (at level 50, left associativity).

Inductive evalR : expr -> val -> Prop :=
  | E_Int : forall (n:nat),
      EInt n \\ intv [n]

  | E_True :
      ETrue \\ boolv [true]

  | E_False :
      EFalse \\ boolv [false]

  | E_NullInt :
      ENullInt \\ intv []

  | E_NullBool :
      ENullBool \\ boolv []

  | E_Not : forall (e1 : expr) v1s,
      e1 \\ boolv v1s ->
      ENot e1 \\ boolv (map negb v1s)

  | E_Max : forall (e1 : expr) v1s,
      e1 \\ intv v1s ->
      EMax e1 \\ intv (to_list (maxo v1s))

  | E_Min : forall (e1 : expr) v1s,
      e1 \\ intv v1s ->
      EMin e1 \\ intv (to_list (mino v1s))

  | E_Sum : forall (e1 : expr) v1s,
      e1 \\ intv v1s ->
      ESum e1 \\ intv [sum v1s]

  | E_Avg : forall (e1 : expr) v1s,
      e1 \\ intv v1s ->
      EAvg e1 \\ intv (to_list (avgo v1s))

  | E_Conj : forall (e1 : expr) v1s,
      e1 \\ boolv v1s ->
      EConj e1 \\ boolv [conj v1s]

  | E_Disj : forall (e1 : expr) v1s,
      e1 \\ boolv v1s ->
      EDisj e1 \\ boolv [disj v1s]

  | E_Count_Int : forall (e1 : expr) v1s,
      e1 \\ intv v1s ->
      ECount e1 \\ intv [length v1s]

  | E_Count_Bool : forall (e1 : expr) v1s,
      e1 \\ boolv v1s ->
      ECount e1 \\ intv [length v1s]

  | E_And : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      EAnd e1 e2 \\ boolv (map (funtuple andb) vtuples)

  | E_Or : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      EOr e1 e2 \\ boolv (map (funtuple orb) vtuples)

  | E_Plus : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s -> 
      vtuples = list_crossproduct v1s v2s ->
      EPlus e1 e2 \\ intv (map (funtuple plus) vtuples)

  | E_Minus : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s -> 
      vtuples = list_crossproduct v1s v2s ->
      EMinus e1 e2 \\ intv (map (funtuple sub) vtuples)

  | E_Mult : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s -> 
      vtuples = list_crossproduct v1s v2s ->
      EMult e1 e2 \\ intv (map (funtuple mul) vtuples)

  | E_Div : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s -> 
      vtuples = list_crossproduct v1s v2s ->
      EDiv e1 e2 \\ intv (fmap (funtuple divo) vtuples)

  | E_Modulo : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s -> 
      vtuples = list_crossproduct v1s v2s ->
      EModulo e1 e2 \\ intv (fmap (funtuple moduloo) vtuples)

  | E_Eq_Int : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      EEq e1 e2 \\ boolv (map (funtuple eqb) vtuples)

  | E_Eq_Bool : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      EEq e1 e2 \\ boolv (map (funtuple beq) vtuples)

  | E_Neq_Int : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      ENeq e1 e2 \\ boolv (map (funtuple neqb) vtuples)

  | E_Neq_Bool : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      ENeq e1 e2 \\ boolv (map (funtuple bneq) vtuples)

  | E_Lt : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      ELt e1 e2 \\ boolv (map (funtuple ltb) vtuples)

  | E_Lte : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      ELte e1 e2 \\ boolv (map (funtuple leb) vtuples)

  | E_Gt : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      EGt e1 e2 \\ boolv (map (funtuple gtb) vtuples)

  | E_Gte : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      EGte e1 e2 \\ boolv (map (funtuple geb) vtuples)

  | E_If_Int : forall (e1 e2 e3 : expr) v1s v2s v3s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ intv v2s ->
      e3 \\ intv v3s ->
      vtuples = list_crossproduct v1s (list_crossproduct v2s v3s) ->
      EIf e1 e2 e3 \\ intv (map iftuple vtuples)

  | E_If_Bool : forall (e1 e2 e3 : expr) v1s v2s v3s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      e3 \\ boolv v3s ->
      vtuples = list_crossproduct v1s (list_crossproduct v2s v3s) ->
      EIf e1 e2 e3 \\ boolv (map iftuple vtuples)

  | E_Concat_Int : forall (e1 e2 : expr) v1s v2s,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      EConcat e1 e2 \\ intv (v1s ++ v2s)

  | E_Concat_Bool : forall (e1 e2 : expr) v1s v2s,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      EConcat e1 e2 \\ boolv (v1s ++ v2s)

  | E_Choice_Int : forall (e1 e2 : expr) v1s v2s,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      EChoice e1 e2 \\ intv (choice v1s v2s)

  | E_Choice_Bool : forall (e1 e2 : expr) v1s v2s,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      EChoice e1 e2 \\ boolv (choice v1s v2s)

  | E_First_Int : forall (e1 : expr) v1s,
      e1 \\ intv v1s ->
      EFirst e1 \\ intv (to_list (hd_error v1s))

  | E_First_Bool : forall (e1 : expr) v1s,
      e1 \\ boolv v1s ->
      EFirst e1 \\ boolv (to_list (hd_error v1s))

  | E_ElemAt_Int : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_pair_with2 v1s v2s ->
      EElemAt e1 e2 \\ intv (fmap (funtuple (@nth_error nat)) vtuples)

  | E_ElemAt_Bool : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_pair_with2 v1s v2s ->
      EElemAt e1 e2 \\ boolv (fmap (funtuple (@nth_error bool)) vtuples)

  | E_IndexOf_Int : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_pair_with2 v1s v2s ->
      EIndexOf e1 e2 \\ intv (fmap (funtuple indexOf_nat) vtuples)

  | E_IndexOf_Bool : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      vtuples = list_pair_with2 v1s v2s ->
      EIndexOf e1 e2 \\ intv (fmap (funtuple indexOf_bool) vtuples)

where "e '\\' v" := (evalR e v) : type_scope.

Fixpoint evalF (e : expr) : option val :=
  match e with
  | EInt n =>
      Some (intv [n])

  | ETrue =>
      Some (boolv [true])

  | EFalse =>
      Some (boolv [false])

  | ENullInt =>
      Some (intv [])

  | ENullBool =>
      Some (boolv [])

  | ENot e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (boolv v1s) =>
          let vs := map negb v1s in
          Some (boolv vs)
      | _ => None
      end

  | EMax e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (intv v1s) =>
          Some (intv (to_list (maxo v1s)))
      | _ => None
      end

  | EMin e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (intv v1s) =>
          Some (intv (to_list (mino v1s)))
      | _ => None
      end

  | ESum e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (intv v1s) =>
          Some (intv [sum v1s])
      | _ => None
      end

  | EAvg e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (intv v1s) =>
          Some (intv (to_list (avgo v1s)))
      | _ => None
      end

  | EConj e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (boolv v1s) =>
          Some (boolv [conj v1s])
      | _ => None
      end

  | EDisj e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (boolv v1s) =>
          Some (boolv [disj v1s])
      | _ => None
      end

  | ECount e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (boolv v1s) =>
          Some (intv [length v1s])
      | Some (intv v1s) =>
          Some (intv [length v1s])
      | _ => None
      end

  | EAnd e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (boolv v1s), Some (boolv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple andb) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | EOr e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (boolv v1s), Some (boolv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple orb) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | EPlus e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple plus) vtuples in
          Some (intv vs)
      | _,_ => None
      end

  | EMinus e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple sub) vtuples in
          Some (intv vs)
      | _,_ => None
      end

  | EMult e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple mul) vtuples in
          Some (intv vs)
      | _,_ => None
      end

  | EDiv e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := fmap (funtuple divo) vtuples in
          Some (intv vs)
      | _,_ => None
      end

  | EModulo e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := fmap (funtuple moduloo) vtuples in
          Some (intv vs)
      | _,_ => None
      end

  | EEq e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple eqb) vtuples in
          Some (boolv vs)
      | Some (boolv v1s), Some (boolv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple beq) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | ENeq e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple neqb) vtuples in
          Some (boolv vs)
      | Some (boolv v1s), Some (boolv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple bneq) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | ELt e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple ltb) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | ELte e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple leb) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | EGt e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple gtb) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | EGte e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple geb) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | EIf e1 e2 e3 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      let v3 := evalF e3 in
      match v1, v2, v3 with
      | Some (boolv v1s), Some (intv v2s), Some (intv v3s) =>
          let vtuples := list_crossproduct v1s (list_crossproduct v2s v3s) in
          let vs := map iftuple vtuples in
          Some (intv vs)
      | Some (boolv v1s), Some (boolv v2s), Some (boolv v3s) =>
          let vtuples := list_crossproduct v1s (list_crossproduct v2s v3s) in
          let vs := map iftuple vtuples in
          Some (boolv vs)
      | _,_,_ => None
      end

  | EConcat e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          Some (intv (v1s ++ v2s))
      | Some (boolv v1s), Some (boolv v2s) =>
          Some (boolv (v1s ++ v2s))
      | _,_ => None
      end

  | EChoice e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          Some (intv (choice v1s v2s))
      | Some (boolv v1s), Some (boolv v2s) =>
          Some (boolv (choice v1s v2s))
      | _,_ => None
      end

  | EFirst e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (intv v1s) =>
          Some (intv (to_list (hd_error v1s)))
      | Some (boolv v1s) =>
          Some (boolv (to_list (hd_error v1s)))
      | _ => None
      end

  | EElemAt e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_pair_with2 v1s v2s in
          let vs := fmap (funtuple (@nth_error nat)) vtuples in
          Some (intv vs)
      | Some (boolv v1s), Some (intv v2s) =>
          let vtuples := list_pair_with2 v1s v2s in
          let vs := fmap (funtuple (@nth_error bool)) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | EIndexOf e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_pair_with2 v1s v2s in
          let vs := fmap (funtuple indexOf_nat) vtuples in
          Some (intv vs)
      | Some (boolv v1s), Some (boolv v2s) =>
          let vtuples := list_pair_with2 v1s v2s in
          let vs := fmap (funtuple indexOf_bool) vtuples in
          Some (intv vs)
      | _,_ => None
      end

  end.

Theorem evalR_eq_evalF: forall e v,
  e \\ v <-> evalF e = Some v.
Proof.
  intros. split.
  - intros.
    induction H.
    all: simpl.
    (* literals *)
    all: try reflexivity.
    (* unops *)
    all: subst.
    all: try (rewrite IHevalR).
    all: try reflexivity.
    (* binops *)
    all: rewrite IHevalR1.
    all: rewrite IHevalR2.
    all: try reflexivity.
    (* if *)
    all: rewrite IHevalR3.
    all: reflexivity.
  - intros.
    generalize dependent v.
    induction e.
    (* literals *)
    all: try (intros ; inversion H ; constructor).
    (* ops *)
    all: intros.
    all: simpl in H.
    (* unops *)
    all: try rename e into e1.
    all: destruct (evalF e1); try congruence.
    (* binops *)
    all: try( destruct (evalF e2); try(destruct v0; congruence)).
    (* if *)
    all: try(
         destruct (evalF e3); try(destruct v0; destruct v1; congruence)).
    all: destruct v0 ; try congruence.
    all: try(destruct v1 ; try congruence).
    all: try(destruct v2 ; try congruence). (* for if *)
    all: destruct v  ; try congruence.
    all: inversion H.

    (* apply constructors *)
    all: econstructor.

    (* equal computed values *)
    all: try reflexivity.

    (* sub expressions *)
    all: try rename IHe into IHe1.
    all: try(apply IHe1 ; reflexivity).
    all: try(apply IHe2 ; reflexivity).
    all: try(apply IHe3 ; reflexivity).
Qed.

Example evalF_1 :
  evalF (EIf ETrue (EInt 3) (EInt 5)) = Some (intv [3]).
Proof. reflexivity. Qed.

Example evalF_2 :
  evalF (EPlus (EInt 3) (EInt 5)) = Some (intv [8]).
Proof. reflexivity. Qed.

Example evalF_3 :
  evalF (EConcat (EInt 3) (EInt 5)) = Some (intv [3; 5]).
Proof. reflexivity. Qed.

Example evalF_4 :
  evalF (ELt (EInt 3) (EInt 5)) = Some (boolv [true]).
Proof. reflexivity. Qed.

Example evalF_5 :
  evalF (ELt (EInt 3) EFalse) = None.
Proof. reflexivity. Qed.

Example evalR_1 :
  (EIf ETrue (EInt 3) (EInt 5)) \\ (intv [3]).
Proof. apply evalR_eq_evalF. reflexivity. Qed.


(***** type checker *****

Literal translation of the typing rules in the (old) NaBL/TS specification
of the IceDust type system. Specification is in
https://github.com/MetaBorgCube/IceDust/releases/tag/v0.6.2
in /icedust/trans/typing/*.ts

Note that in the new NaBL2 type system specification types, multiplicities,
and calculation strategies are inside a single tuple, so it is harder to see
the correspondence. Specification is in
https://github.com/MetaBorgCube/IceDust/tree/master/icedust/trans/analysis
in expressions-*.nabl2

The NaBL/TS and NaBL2 specification are exercised by the same 500 tests,
so we are reasonably confident that they are equal. *)

Reserved Notation "e ':' t"
                  (at level 50, left associativity).

Inductive typeR : expr -> type -> Prop :=
  | T_Int : forall (n:nat),
      EInt n : intty

  | T_True :
      ETrue : boolty

  | T_False :
      EFalse : boolty

  | T_NullInt :
      ENullInt : intty

  | T_NullBool :
      ENullBool : boolty

  | T_Not : forall (e1 : expr),
      e1 : boolty ->
      ENot e1 : boolty

  | T_Max : forall (e1 : expr),
      e1 : intty ->
      EMax e1 : intty

  | T_Min : forall (e1 : expr),
      e1 : intty ->
      EMin e1 : intty

  | T_Sum : forall (e1 : expr),
      e1 : intty ->
      ESum e1 : intty

  | T_Avg : forall (e1 : expr),
      e1 : intty ->
      EAvg e1 : intty

  | T_Conj : forall (e1 : expr),
      e1 : boolty ->
      EConj e1 : boolty

  | T_Disj : forall (e1 : expr),
      e1 : boolty ->
      EDisj e1 : boolty

  | T_Count : forall (e1 : expr) t1,
      e1 : t1 ->
      ECount e1 : intty

  | T_And : forall (e1 e2 : expr),
      e1 : boolty ->
      e2 : boolty ->
      EAnd e1 e2 : boolty

  | T_Or : forall (e1 e2 : expr),
      e1 : boolty ->
      e2 : boolty ->
      EOr e1 e2 : boolty

  | T_Plus : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EPlus e1 e2 : intty

  | T_Minus : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EMinus e1 e2 : intty

  | T_Mult : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EMult e1 e2 : intty

  | T_Div : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EDiv e1 e2 : intty

  | T_Modulo : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EModulo e1 e2 : intty

  | T_Eq : forall (e1 e2 : expr) t1,
      e1 : t1 ->
      e2 : t1 ->
      EEq e1 e2 : boolty

  | T_Neq : forall (e1 e2 : expr) t1,
      e1 : t1 ->
      e2 : t1 ->
      ENeq e1 e2 : boolty

  | T_Lt : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      ELt e1 e2 : boolty

  | T_Lte : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      ELte e1 e2 : boolty

  | T_Gt : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EGt e1 e2 : boolty

  | T_Gte : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EGte e1 e2 : boolty

  | T_If : forall (e1 e2 e3 : expr) t1,
      e1 : boolty ->
      e2 : t1 ->
      e3 : t1 ->
      EIf e1 e2 e3 : t1

  | T_Concat : forall (e1 e2 : expr) t1,
      e1 : t1 ->
      e2 : t1 ->
      EConcat e1 e2 : t1

  | T_Choice : forall (e1 e2 : expr) t1,
      e1 : t1 ->
      e2 : t1 ->
      EChoice e1 e2 : t1

  | T_First : forall (e1 : expr) t1,
      e1 : t1 ->
      EFirst e1 : t1

  | T_ElemAt : forall (e1 e2 : expr) t1,
      e1 : t1 ->
      e2 : intty ->
      EElemAt e1 e2 : t1

  | T_IndexOf : forall (e1 e2 : expr) t1,
      e1 : t1 ->
      e2 : t1 ->
      EIndexOf e1 e2 : intty

where "e ':' t" := (typeR e t) : type_scope.

Fixpoint typeF (e : expr) : option type :=
  match e with
  | EInt n =>
      Some intty

  | ETrue =>
      Some boolty

  | EFalse =>
      Some boolty

  | ENullInt =>
      Some intty

  | ENullBool =>
      Some boolty

  | ENot e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some boolty =>
          Some boolty
      | _ => None
      end

  | EMax e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some intty =>
          Some intty
      | _ => None
      end

  | EMin e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some intty =>
          Some intty
      | _ => None
      end

  | ESum e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some intty =>
          Some intty
      | _ => None
      end

  | EAvg e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some intty =>
          Some intty
      | _ => None
      end

  | EConj e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some boolty =>
          Some boolty
      | _ => None
      end

  | EDisj e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some boolty =>
          Some boolty
      | _ => None
      end

  | ECount e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some _ =>
          Some intty
      | _ => None
      end

  | EAnd e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some boolty, Some boolty =>
          Some boolty
      | _,_ => None
      end

  | EOr e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some boolty, Some boolty =>
          Some boolty
      | _,_ => None
      end

  | EPlus e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | _,_ => None
      end

  | EMinus e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | _,_ => None
      end

  | EMult e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | _,_ => None
      end

  | EDiv e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | _,_ => None
      end

  | EModulo e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | _,_ => None
      end

  | EEq e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some boolty
      | Some boolty, Some boolty =>
          Some boolty
      | _,_ => None
      end

  | ENeq e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some boolty
      | Some boolty, Some boolty =>
          Some boolty
      | _,_ => None
      end

  | ELt e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some boolty
      | _,_ => None
      end

  | ELte e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some boolty
      | _,_ => None
      end

  | EGt e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some boolty
      | _,_ => None
      end

  | EGte e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some boolty
      | _,_ => None
      end

  | EIf e1 e2 e3 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      let t3 := typeF e3 in
      match t1, t2, t3 with
      | Some boolty, Some intty, Some intty =>
          Some intty
      | Some boolty, Some boolty, Some boolty =>
          Some boolty
      | _,_,_ => None
      end

  | EConcat e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | Some boolty, Some boolty =>
          Some boolty
      | _,_ => None
      end

  | EChoice e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | Some boolty, Some boolty =>
          Some boolty
      | _,_ => None
      end

  | EFirst e1 =>
      let t1 := typeF e1 in
      t1

  | EElemAt e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some ty, Some intty =>
          Some ty
      | _,_ => None
      end

  | EIndexOf e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
      | Some boolty, Some boolty =>
          Some intty
      | _,_ => None
      end

  end.

Theorem typeR_eq_typeF: forall e t,
  e : t <-> typeF e = Some t.
Proof.
  intros. split.
  - intros.
    induction H.
    (* literals *)
    all: try(reflexivity).
    (* unops *)
    all: try rename IHtypeR into IHtypeR1.
    all: simpl.
    all: subst.
    all: rewrite IHtypeR1.
    all: try destruct t1.
    all: try reflexivity.
    (* binops *)
    all: rewrite IHtypeR2.
    all: try reflexivity.
    (* if *)
    all: rewrite IHtypeR3.
    all: try reflexivity.
  - generalize dependent t.
    induction e.
    (* literals *)
    all: try (intros ; inversion H ; constructor).
    (* unops *)
    all: intros.
    all: simpl in H.
    all: try rename IHe into IHe1.
    all: try rename e into e1.
    all: destruct (typeF e1); try congruence.
    (* binops *)
    all: try(destruct (typeF e2); try(destruct t0; congruence)).
    (* if *)
    all: try(
         destruct (typeF e3); try(destruct t0; destruct t1; congruence)).
    all: destruct t0 ; try congruence.
    all: try(destruct t1 ; try congruence).
    all: try(destruct t2 ; try congruence).
    all: destruct t  ; try congruence.
    all: try(econstructor).
    all: try(apply IHe1; reflexivity).
    all: try(apply IHe2; reflexivity).
    all: try(apply IHe3; reflexivity).
Qed.

Example typeR_1 :
  (EPlus (EInt 1) (EInt 2)) : intty.
Proof. apply typeR_eq_typeF. simpl. reflexivity. Qed.

(***** multiplicity checker *****

Specification in same place as type checker. *)

Definition mult_crossproduct (m1 : mult) (m2 : mult) : mult :=
  match m1, m2 with
  | one       , m2         => m2
  | m1        , one        => m1
  | zeroOrOne , zeroOrOne  => zeroOrOne
  | oneOrMore , oneOrMore  => oneOrMore
  | _         , _          => zeroOrMore
  end.

Definition mult_concat (m1 : mult) (m2 : mult) : mult :=
  match m1, m2 with
  | oneOrMore, _         => oneOrMore
  | _        , oneOrMore => oneOrMore
  | one      , _         => oneOrMore
  | _        , one       => oneOrMore
  | _        , _         => zeroOrMore
  end.

Definition mult_choice (m1 : mult) (m2 : mult) : mult :=
  match m1, m2 with
  | one      , _         => one
  | oneOrMore, _         => oneOrMore
  | zeroOrOne, _         => m2
  | _        , one       => oneOrMore
  | _        , oneOrMore => oneOrMore
  | _        , _         => zeroOrMore
  end.

Definition mult_lower_zero (m1 : mult): mult :=
  match m1 with
  | one       => zeroOrOne
  | oneOrMore => zeroOrMore
  | m1        => m1
  end.

Definition mult_upper_one (m1 : mult): mult :=
  match m1 with
  | zeroOrMore => zeroOrOne
  | oneOrMore  => one
  | m1         => m1
  end.

Reserved Notation "e '~' m"
                  (at level 50, left associativity).

Inductive multR : expr -> mult -> Prop :=
  | M_Int : forall (n:nat),
      EInt n ~ one

  | M_True :
      ETrue ~ one

  | M_False :
      EFalse ~ one

  | M_NullInt :
      ENullInt ~ zeroOrOne

  | M_NullBool :
      ENullBool ~ zeroOrOne

  | M_Not : forall (e1 : expr) m1,
      e1 ~ m1 ->
      ENot e1 ~ m1

  | M_Max : forall (e1 : expr) m1,
      e1 ~ m1 ->
      EMax e1 ~ mult_upper_one m1

  | M_Min : forall (e1 : expr) m1,
      e1 ~ m1 ->
      EMin e1 ~ mult_upper_one m1

  | M_Sum : forall (e1 : expr) m1,
      e1 ~ m1 ->
      ESum e1 ~ one

  | M_Avg : forall (e1 : expr) m1,
      e1 ~ m1 ->
      EAvg e1 ~ mult_upper_one m1

  | M_Conj : forall (e1 : expr) m1,
      e1 ~ m1 ->
      EConj e1 ~ one

  | M_Disj : forall (e1 : expr) m1,
      e1 ~ m1 ->
      EDisj e1 ~ one

  | M_Count : forall (e1 : expr) m1,
      e1 ~ m1 ->
      ECount e1 ~ one

  | M_And : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EAnd e1 e2 ~ mult_crossproduct m1 m2

  | M_Or : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EOr e1 e2 ~ mult_crossproduct m1 m2

  | M_Plus : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EPlus e1 e2 ~ mult_crossproduct m1 m2

  | M_Minus : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EMinus e1 e2 ~ mult_crossproduct m1 m2

  | M_Mult : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EMult e1 e2 ~ mult_crossproduct m1 m2

  | M_Div : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EDiv e1 e2 ~ mult_lower_zero (mult_crossproduct m1 m2)

  | M_Modulo : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EModulo e1 e2 ~ mult_lower_zero (mult_crossproduct m1 m2)

  | M_Eq : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EEq e1 e2 ~ mult_crossproduct m1 m2

  | M_Neq : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      ENeq e1 e2 ~ mult_crossproduct m1 m2

  | M_Lt : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      ELt e1 e2 ~ mult_crossproduct m1 m2

  | M_Lte : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      ELte e1 e2 ~ mult_crossproduct m1 m2

  | M_Gt : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EGt e1 e2 ~ mult_crossproduct m1 m2

  | M_Gte : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EGte e1 e2 ~ mult_crossproduct m1 m2

  | M_If : forall (e1 e2 e3 : expr) m1 m2 m3,
      e1 ~ m1 ->
      e2 ~ m2 ->
      e3 ~ m3 ->
      EIf e1 e2 e3 ~ mult_crossproduct m1 (mult_crossproduct m2 m3)

  | M_Concat : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EConcat e1 e2 ~ mult_concat m1 m2

  | M_Choice : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EChoice e1 e2 ~ mult_choice m1 m2

  | M_First : forall (e1 : expr) m1,
      e1 ~ m1 ->
      EFirst e1 ~ mult_upper_one m1

  | M_ElemAt : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EElemAt e1 e2 ~ mult_lower_zero m2

  | M_IndexOf : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EIndexOf e1 e2 ~ mult_lower_zero m2

where "e '~' m" := (multR e m) : type_scope.

Fixpoint multF (e : expr) : mult :=
  match e with
  | EInt n =>
      one

  | ETrue =>
      one

  | EFalse =>
      one

  | ENullInt =>
      zeroOrOne

  | ENullBool =>
      zeroOrOne

  | ENot e1 =>
      let m1 := multF e1 in
      m1

  | EMax e1 =>
      let m1 := multF e1 in
      mult_upper_one m1

  | EMin e1 =>
      let m1 := multF e1 in
      mult_upper_one m1

  | ESum e1 =>
      let m1 := multF e1 in
      one

  | EAvg e1 =>
      let m1 := multF e1 in
      mult_upper_one m1

  | EConj e1 =>
      let m1 := multF e1 in
      one

  | EDisj e1 =>
      let m1 := multF e1 in
      one

  | ECount e1 =>
      let m1 := multF e1 in
      one

  | EAnd e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EOr e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EPlus e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EMinus e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EMult e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EDiv e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_lower_zero (mult_crossproduct m1 m2)

  | EModulo e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_lower_zero (mult_crossproduct m1 m2)

  | EEq e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | ENeq e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | ELt e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | ELte e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EGt e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EGte e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | EIf e1 e2 e3 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      let m3 := multF e3 in
      mult_crossproduct m1 (mult_crossproduct m2 m3)

  | EConcat e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_concat m1 m2

  | EChoice e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_choice m1 m2

  | EFirst e1 =>
      let m1 := multF e1 in
      mult_upper_one m1

  | EElemAt e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_lower_zero m2

  | EIndexOf e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_lower_zero m2

  end.

Theorem multR_eq_multF: forall e m,
  e ~ m <-> multF e = m.
Proof.
  split.
  - intros.
    induction H ;
    try (simpl ; subst ; reflexivity).
  - generalize dependent m.
    induction e.
    all: intros.
    all: simpl in H.
    all: subst.
    all: econstructor.
    all: try rename IHe into IHe1.
    all: try(apply IHe1).
    all: try(apply IHe2).
    all: try(apply IHe3).
    all: reflexivity.
Qed.

Example multR_1 :
  (EPlus (EInt 1) (EInt 2)) ~ one.
Proof. apply multR_eq_multF. simpl. reflexivity. Qed.

Example multR_2 :
  (EConcat (EInt 1) (EInt 2)) ~ oneOrMore.
Proof. apply multR_eq_multF. simpl. reflexivity. Qed.


(***** aux functions for proving type- and multiplicity soundness *****)
Definition valty (v : val) : type :=
  match v with
  | intv  _ => intty
  | boolv _ => boolty
  end.

Inductive mult_containsR: mult -> val -> Prop :=
  | M_ZeroOrMore : forall v,
      mult_containsR zeroOrMore v
  | M_One_Int : forall m v,
      mult_containsR m (intv [v])
  | M_One_Bool : forall m v,
      mult_containsR m (boolv [v])
  | M_ZeroOrOne_Int :
      mult_containsR zeroOrOne (intv [])
  | M_ZeroOrOne_Bool :
      mult_containsR zeroOrOne (boolv [])
  | M_OneOrMore_Int : forall v vs,
      mult_containsR oneOrMore (intv (v::vs))
  | M_OneOrMore_Bool : forall v vs,
      mult_containsR oneOrMore (boolv (v::vs))
.

Definition mult_containsF (m : mult) (v : val) : bool :=
  match m, v with
  | zeroOrMore, _             => true
  | _         , intv  [v]     => true
  | _         , boolv [v]     => true
  | zeroOrOne , intv  []      => true
  | zeroOrOne , boolv []      => true
  | oneOrMore , intv  (v::vs) => true
  | oneOrMore , boolv (v::vs) => true
  | _         , _             => false
  end.

Theorem mult_containsR_eq_mult_containsF : forall m v,
  mult_containsR m v <-> mult_containsF m v = true.
Proof.
  intros. split.
  - intros.
    induction H;
    try( simpl; reflexivity);
    try( destruct m; simpl; reflexivity);
    try( simpl ; destruct vs; reflexivity).
  - generalize dependent v.
    induction m;
    intros;
    (* destruct all possible cases *)
    destruct v; destruct l; try destruct l;
    (* all possible cases are either not possible, or a constructor *)
    try inversion H; try congruence; try constructor.
Qed.

(***** type preservation *****)
Ltac specialize_auto :=
  match goal with
    H1 : ?A -> ?B,
    H2 : ?A
    |- _ => specialize (H1 H2)
  end.

Theorem type_preservation : forall (e : expr) t v,
  e : t ->
  e \\ v ->
  valty v = t.
Proof.
  intros e t v Htype Hval.
  induction Hval.
  all: simpl.
  (* get types of sub expressions *)
  all: inversion Htype.
  all: try reflexivity.
  all: subst.
  (* extract types from values *)
  all: repeat specialize_auto.
  all: try simpl in IHHval1.
  all: try simpl in IHHval2.
  all: try simpl in IHHval3.
  all: subst.
  all: reflexivity.
Qed.

(***** completeness *****)
Lemma exists_some: forall {X:Type} (v1:X),
  exists v2 : X,
    Some v1 =
    Some v2.
Proof.
  eauto.
Qed.

Ltac case_match :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:?
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.

Theorem typed_evalF_totality : forall (e : expr) t,
  e : t ->
  exists v,
  evalF e = Some v.
Proof.
  intros.
  induction H.
  (* literals *)
  all: try(apply exists_some).
  (* unops *)
  all: simpl.
  all: try rename IHtypeR into IHtypeR1.
  all: destruct IHtypeR1 as [v1 Hv1].
  all: rewrite Hv1.
  all: apply evalR_eq_evalF in Hv1.
  all: apply type_preservation with (v:=v1) in H ; try assumption.
  all: unfold valty in H.
  all: case_match; try congruence.
  all: try apply exists_some.
  (* binops *)
  all: destruct IHtypeR2 as [v2 Hv2].
  all: rewrite Hv2.
  all: apply evalR_eq_evalF in Hv2.
  all: apply type_preservation with (v:=v2) in H0 ; try assumption.
  all: unfold valty in H0.
  all: case_match; try congruence.
  all: try apply exists_some.
  (* if *)
  all: destruct IHtypeR3 as [v3 Hv3].
  all: rewrite Hv3.
  all: apply evalR_eq_evalF in Hv3.
  all: apply type_preservation with (v:=v3) in H1 ; try assumption.
  all: subst.
  all: unfold valty in H1.
  all: case_match; try congruence.
  all: apply exists_some.
Qed.

Theorem typed_evalR_totality : forall (e : expr) t,
  e : t ->
  exists v,
  e \\ v.
Proof.
  intros.
  apply typed_evalF_totality in H.
  destruct H.
  exists x.
  apply evalR_eq_evalF in H.
  assumption.
Qed.

(***** multiplicity preservation *****)
Ltac specialize_int :=
  match goal with
    H : forall t : type, ?E : t -> mult_containsR ?M (intv ?V)
    |- _ => specialize (H intty)
  end.
Ltac specialize_bool :=
  match goal with
    H : forall t : type, ?E : t -> mult_containsR ?M (boolv ?V)
    |- _ => specialize (H boolty)
  end.

Ltac expression_type_int :=
  match goal with
    H1 : ?E2 \\ intv ?V,
    H2 : ?E2 : ?T
    |- _ =>
    assert (HexpressionType : E2 : T); try assumption;
    destruct T;
    apply type_preservation with (v:=intv V) in HexpressionType;
    try assumption;
    inversion HexpressionType
  end.
Ltac expression_type_bool :=
  match goal with
    H1 : ?E2 \\ boolv ?V,
    H2 : ?E2 : ?T
    |- _ =>
    assert (HexpressionType : E2 : T); try assumption;
    destruct T;
    apply type_preservation with (v:=boolv V) in HexpressionType;
    try assumption;
    inversion HexpressionType
  end.

Theorem mult_preservation : forall (e : expr) t m v,
  e : t ->
  e ~ m ->
  e \\ v ->
  mult_containsR m v.
Proof.
  intros e t m v Htype Hmult Hval.
  generalize dependent t.
  generalize dependent m.
  induction Hval.
  all: intros.
  (* proof literals of mult one *)
  all: try(simpl; constructor).
  (* get multiplicities of sub expressions *)
  all: inversion Hmult.
  all: subst.
  (* proof null literals *)
  all: try constructor.
  (* get types of sub expressions *)
  all: inversion Htype.
  all: subst.
  (* find sub expression types with type preservation *)
  all: try rename t into t1.
  all: try expression_type_int.
  all: try expression_type_bool.
  (* specialize induction hypotheses to type and mult from sub exprs *)
  all: try rename m into m1.
  all: try rename IHHval into IHHval1.
  all: specialize (IHHval1 m1).
  all: try(specialize (IHHval2 m2)).
  all: try(specialize (IHHval3 m3)).
  all: repeat specialize_auto.
  all: repeat specialize_int.
  all: repeat specialize_bool.
  all: repeat specialize_auto.
  (* destruct multiplicities and values *)
  all : rewrite mult_containsR_eq_mult_containsF in *.
  all : destruct m1.
  all : simpl in IHHval1.
  all : destruct v1s ; try congruence.
  all : try destruct v1s ; try congruence.
  all : try reflexivity.
  all : destruct m2.
  all : simpl in IHHval2.
  all : destruct v2s ; try congruence.
  all : try destruct v2s ; try congruence.
  all : try reflexivity.
  all : try destruct m3.
  all : try simpl in IHHval3.
  all : try destruct v3s ; try congruence.
  all : try destruct v3s ; try congruence.
  all : try reflexivity.
  (* cases with optionals *)
  all : simpl.
  all : case_match; try reflexivity.
  all : case_match.
  all : inversion Heql.
  all : reflexivity.
Qed.
