Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.

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

(***** signatures *****)
Inductive expr : Type :=
  | EInt    : nat -> expr
  | ETrue   : expr
  | EFalse  : expr
  | EPlus   : expr -> expr -> expr
  | ELt     : expr -> expr -> expr
  | EIf     : expr -> expr -> expr -> expr
  | EConcat : expr -> expr -> expr.

Inductive ty : Type :=
  | intty  : ty
  | boolty : ty.

Inductive mult : Type :=
  | one : mult
  | zeroOrOne : mult
  | oneOrMore : mult
  | zeroOrMore : mult.

Inductive val : Type :=
  | intv  : list nat -> val
  | boolv : list bool -> val.


(***** eval : expr -> ty *****)
Function plustuple (t : (nat*nat)) : nat :=
  match t with
  | (n1, n2) => n1 + n2
  end.

Function lttuple (t : (nat*nat)) : bool :=
  match t with
  | (n1, n2) => n1 <? n2
  end.

Function iftuple {X : Type} (t : (bool*(X*X))) : X :=
  match t with
  | (true,  (_ , v3)) => v3
  | (false, (v2, _ )) => v2
  end.

Reserved Notation "e '\\' v"
                  (at level 50, left associativity).

Inductive evalR : expr -> val -> Prop :=
  | E_Int : forall (n:nat),
      EInt n \\ intv [n]

  | E_True :
      ETrue \\ boolv [true]

  | E_False :
      EFalse \\ boolv [false]

  | E_Plus : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      EPlus e1 e2 \\ intv (map plustuple vtuples)

  | E_Lt : forall (e1 e2 : expr) v1s v2s vtuples,
      e1 \\ intv v1s ->
      e2 \\ intv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      ELt e1 e2 \\ boolv (map lttuple vtuples)

  | E_If_Int : forall (e1 e2 e3 : expr) v1s v2s v3s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ intv v2s ->
      e3 \\ intv v3s -> (* IceDust does not shortcut evaluation *)
      vtuples = list_crossproduct v1s (list_crossproduct v2s v3s) ->
      EIf e1 e2 e3 \\ intv (map iftuple vtuples)

  | E_If_Bool : forall (e1 e2 e3 : expr) v1s v2s v3s vtuples,
      e1 \\ boolv v1s ->
      e2 \\ boolv v2s ->
      e3 \\ boolv v3s -> (* IceDust does not shortcut evaluation *)
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

where "e '\\' v" := (evalR e v) : type_scope.

Fixpoint evalF (e : expr) : option val :=
  match e with
  | EInt n =>
      Some (intv [n])

  | ETrue =>
      Some (boolv [true])

  | EFalse =>
      Some (boolv [false])

  | EPlus e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map plustuple vtuples in
          Some (intv vs)
      | _,_ => None
      end

  | ELt e1 e2 =>
      let v1 := evalF e1 in
      let v2 := evalF e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map lttuple vtuples in
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

  end.

Theorem evalR_eq_evalF: forall e v,
  e \\ v <-> evalF e = Some v.
Proof.
  intros. split.
  - intros.
    induction H ;
    try (simpl ; reflexivity); (* literals *)
    try (simpl ; subst ; rewrite IHevalR1 ; rewrite IHevalR2 ;
         reflexivity ); (* binops *)
    try (simpl ; subst ; rewrite IHevalR1 ; rewrite IHevalR2 ;
         rewrite IHevalR3 ; reflexivity ). (* if *)
  - intros.
    generalize dependent v.
    induction e ;
    try (intros ; inversion H ; constructor) (* literals *)
    .
    + intros.
      simpl in H.
      destruct (evalF e1) ; try congruence.
      destruct (evalF e2) ; try (destruct v0 ; congruence).
      destruct v0 ; try congruence.
      destruct v1 ; try congruence.
      destruct v  ; try congruence.
      inversion H.
      apply E_Plus with (v1s:=l) (v2s:=l0).
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
      reflexivity.
    + intros.
      simpl in H.
      destruct (evalF e1) ; try congruence.
      destruct (evalF e2) ; try (destruct v0 ; congruence).
      destruct v0 ; try congruence.
      destruct v1 ; try congruence.
      destruct v  ; try congruence.
      inversion H.
      apply E_Lt with (v1s:=l) (v2s:=l0).
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
      reflexivity.
    + intros.
      simpl in H.
      destruct (evalF e1) ; try congruence.
      destruct (evalF e2) ; try (destruct v0 ; congruence).
      destruct (evalF e3).
      destruct v0 ; try congruence.
      destruct v1 ; try congruence.
      destruct v2 ; try congruence.
      destruct v  ; try congruence.
      inversion H.
      apply E_If_Int with (v1s:=l) (v2s:=l0) (v3s:=l1).
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
      apply IHe3. reflexivity.
      reflexivity.
      destruct v2 ; try congruence.
      destruct v  ; try congruence.
      inversion H.
      apply E_If_Bool with (v1s:=l) (v2s:=l0) (v3s:=l1).
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
      apply IHe3. reflexivity.
      reflexivity.
      destruct v0.
      congruence.
      destruct v1.
      congruence.
      congruence.
    + intros.
      simpl in H.
      destruct (evalF e1) ; try congruence.
      destruct (evalF e2) ; try (destruct v0 ; congruence).
      destruct v0 ; try congruence.
      destruct v1 ; try congruence.
      destruct v  ; try congruence.
      inversion H.
      apply E_Concat_Int with (v1s:=l) (v2s:=l0).
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
      destruct v1 ; try congruence.
      destruct v  ; try congruence.
      inversion H.
      apply E_Concat_Bool with (v1s:=l) (v2s:=l0).
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
Qed.

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
