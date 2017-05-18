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
  | intl : nat -> expr
  | plus : expr -> expr -> expr.

Inductive ty : Type :=
  | intty : ty.

Inductive mult : Type :=
  | one : mult
  | zeroOrOne : mult
  | oneOrMore : mult
  | zeroOrMore : mult.

Inductive val : Type :=
  | intv : nat -> val.

(***** type check *****)
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
  end.

Example test_tc_1 :
tc (plus (intl 1) (intl 2)) = intty.
Proof. simpl. reflexivity. Qed.

(***** multiplicity check *****)
(* TODO: lattice as in NaBL2? or keep as function? *)
Definition mult_crossproduct (m1 : mult) (m2 : mult) : mult :=
  match m1, m2 with
  | one       , m2         => m2
  | m1        , one        => m1
  | zeroOrOne , zeroOrOne  => zeroOrOne
  | oneOrMore , oneOrMore  => oneOrMore
  | _         , _          => zeroOrMore
  end.

Fixpoint mc (e : expr) : mult :=
  match e with
  | intl _ => one
  | plus e1 e2 =>
      let m1 := mc e1 in
      let m2 := mc e2 in
      mult_crossproduct m1 m2
  end.

Example test_mc_1 :
mc (plus (intl 1) (intl 2)) = one.
Proof. simpl. reflexivity. Qed.

(***** interpreter *****)
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
  end.

Example test_eval_1 :
eval (plus (intl 1) (intl 2)) = [intv 3].
Proof. simpl. reflexivity. Qed.
