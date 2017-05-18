Require Import List.
Import ListNotations.

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

Fixpoint list_crossproduct {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx with
  | [] => []
  | x :: tx => (list_pair_with2 x ly) ++ (list_crossproduct tx ly)
  end.

(***** signatures *****)
Inductive expr : Type :=
  | intl   : nat -> expr
  | plus   : expr -> expr -> expr
  | concat : expr -> expr -> expr.

Inductive ty : Type :=
  | intty : ty.

Inductive mult : Type :=
  | one : mult
  | zeroOrOne : mult
  | oneOrMore : mult
  | zeroOrMore : mult.

Inductive val : Type :=
  | intv : nat -> val.

(***** type check : expr -> ty *****)
(* TODO: needs to be a partial function *)
Fixpoint tc (e : expr) : ty :=
  match e with
  | intl _ => intty
  | plus e1 e2 => 
      let t1 := tc e1 in
      let t2 := tc e2 in
      match t1, t2 with
      | intty, intty => intty
      end
  | concat e1 e2 =>
      let t1 := tc e1 in
      let t2 := tc e2 in
      t1 (* TODO: check equality *)
  end.

Example test_tc_1 :
tc (plus (intl 1) (intl 2)) = intty.
Proof. simpl. reflexivity. Qed.

(***** multiplicity check : expr -> mult *****)
(* TODO: lattice as in NaBL2? or keep as function? *)
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

Fixpoint mc (e : expr) : mult :=
  match e with
  | intl _ => one
  | plus e1 e2 =>
      let m1 := mc e1 in
      let m2 := mc e2 in
      mult_crossproduct m1 m2
  | concat e1 e2 =>
      let m1 := mc e1 in
      let m2 := mc e2 in
      mult_concat m1 m2
  end.

Example test_mc_1 :
mc (plus (intl 1) (intl 2)) = one.
Proof. simpl. reflexivity. Qed.

Example test_mc_2 :
mc (concat (intl 1) (intl 2)) = oneOrMore.
Proof. simpl. reflexivity. Qed.

(***** interpreter : expr -> list val *****)
Definition eval_plus (v : val * val) : val :=
  match v with
  | (intv n1, intv n2) => intv (n1 + n2)
  end.

Fixpoint eval (b : expr) : list val :=
  match b with
  | intl n => [(intv n)]
  | plus e1 e2 =>
      let v1 : list val       := eval e1 in
      let v2 : list val       := eval e2 in
      let vs : list (val*val) := list_crossproduct v1 v2 in
      map eval_plus vs
  | concat e1 e2 =>
      let v1 : list val       := eval e1 in
      let v2 : list val       := eval e2 in
      v1 ++ v2
  end.

Example test_eval_1 :
eval (plus (intl 1) (intl 2)) = [intv 3].
Proof. simpl. reflexivity. Qed.

Example test_eval_2 :
eval (plus (intl 1) (concat (intl 2) (intl 3))) = [intv 3; intv 4].
Proof. simpl. reflexivity. Qed.

(***** type of value : list val -> ty *****)
Definition tv1 (v : val) : ty :=
  match v with
  | intv _ => intty
  end.

(* TODO: 1. how to represent no value? *)
(* TODO: 2. make partial function, if contains values from different types *)
Fixpoint tv (vs : list val) : ty :=
  match vs with
  | [] => intty (* FIXME: *)
  | v :: vs => tv1 v (* FIXME: *)
  end.

(***** multiplicity of value : list val -> mult *****)
Definition mv (vs : list val) : mult :=
  match vs with
  | [] => zeroOrOne
  | [_] => one
  | _ => oneOrMore
  end.

Definition mult_contains (m1 : mult) (m2 : mult) : bool :=
  match m1, m2 with
  | zeroOrMore, _         => true
  | _         , one       => true
  | zeroOrOne , zeroOrOne => true
  | oneOrMore , oneOrMore => true
  | _         , _         => false
  end.

(***** multiplicity preservation *****)
Theorem mult_perservation : forall (e : expr),
  mult_contains (mc e) (mv (eval e)) = true.
Proof.
  induction e.
  - simpl. reflexivity.
  - simpl.
Abort. (* here is where the fun starts *)
