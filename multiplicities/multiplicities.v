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


(***** eval : expr -> val *****)
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
  | (true,  (v2, _ )) => v2
  | (false, (_ , v3)) => v3
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
    + (* if *)
      intros.
      simpl in H.
      destruct (evalF e1) ; try congruence.
      destruct (evalF e2) ; try (destruct v0 ; congruence).
      destruct (evalF e3) ; try (destruct v0 ; destruct v1 ; congruence).
      destruct v0 ; try congruence.
      destruct v1 ; try congruence.
      * (* int *)
        destruct v2 ; try congruence.
        destruct v  ; try congruence.
        inversion H.
        apply E_If_Int with (v1s:=l) (v2s:=l0) (v3s:=l1).
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
        apply IHe3. reflexivity.
        reflexivity.
      * (* bool *)
        destruct v2 ; try congruence.
        destruct v  ; try congruence.
        inversion H.
        apply E_If_Bool with (v1s:=l) (v2s:=l0) (v3s:=l1).
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
        apply IHe3. reflexivity.
        reflexivity.
    + (* concat *)
      intros.
      simpl in H.
      destruct (evalF e1) ; try congruence.
      destruct (evalF e2) ; try (destruct v0 ; congruence).
      destruct v0.
      * (* int *)
        destruct v1 ; try congruence.
        destruct v  ; try congruence.
        inversion H.
        apply E_Concat_Int with (v1s:=l) (v2s:=l0).
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
      * (* bool *)
        destruct v1 ; try congruence.
        destruct v  ; try congruence.
        inversion H.
        apply E_Concat_Bool with (v1s:=l) (v2s:=l0).
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
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


(***** type check : expr -> ty *****)
Reserved Notation "e ':' t"
                  (at level 50, left associativity).

Inductive typeR : expr -> type -> Prop :=
  | T_Int : forall (n:nat),
      EInt n : intty

  | T_True :
      ETrue : boolty

  | T_False :
      EFalse : boolty

  | T_Plus : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EPlus e1 e2 : intty

  | T_Lt : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      ELt e1 e2 : boolty

  | T_If_Int : forall (e1 e2 e3 : expr),
      e1 : boolty ->
      e2 : intty ->
      e3 : intty ->
      EIf e1 e2 e3 : intty

  | T_If_Bool : forall (e1 e2 e3 : expr),
      e1 : boolty ->
      e2 : boolty ->
      e3 : boolty ->
      EIf e1 e2 e3 : boolty

  | T_Concat_Int : forall (e1 e2 : expr),
      e1 : intty ->
      e2 : intty ->
      EConcat e1 e2 : intty

  | T_Concat_Bool : forall (e1 e2 : expr),
      e1 : boolty ->
      e2 : boolty ->
      EConcat e1 e2 : boolty

where "e ':' t" := (typeR e t) : type_scope.

Fixpoint typeF (e : expr) : option type :=
  match e with
  | EInt n =>
      Some intty

  | ETrue =>
      Some boolty

  | EFalse =>
      Some boolty

  | EPlus e1 e2 =>
      let t1 := typeF e1 in
      let t2 := typeF e2 in
      match t1, t2 with
      | Some intty, Some intty =>
          Some intty
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

  end.

Theorem typeR_eq_typeF: forall e t,
  e : t <-> typeF e = Some t.
Proof.
  intros. split.
  - intros.
    induction H ;
    try (simpl ; reflexivity); (* literals *)
    try (simpl ; subst ; rewrite IHtypeR1 ; rewrite IHtypeR2 ;
         reflexivity ); (* binops *)
    try (simpl ; subst ; rewrite IHtypeR1 ; rewrite IHtypeR2 ;
         rewrite IHtypeR3 ; reflexivity ). (* if *)  
  - generalize dependent t.
    induction e ;
    try (intros ; inversion H ; constructor). (* literals *)
    + intros.
      simpl in H.
      destruct (typeF e1) ; try congruence.
      destruct (typeF e2) ; try (destruct t0 ; congruence).
      destruct t0 ; try congruence.
      destruct t1 ; try congruence.
      destruct t  ; try congruence.
      apply T_Plus.
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
    + intros.
      simpl in H.
      destruct (typeF e1) ; try congruence.
      destruct (typeF e2) ; try (destruct t0 ; congruence).
      destruct t0 ; try congruence.
      destruct t1 ; try congruence.
      destruct t  ; try congruence.
      apply T_Lt.
      apply IHe1. reflexivity.
      apply IHe2. reflexivity.
    + (* if *)
      intros.
      simpl in H.
      destruct (typeF e1) ; try congruence.
      destruct (typeF e2) ; try (destruct t0 ; congruence).
      destruct (typeF e3) ; try (destruct t0 ; destruct t1 ; congruence).
      destruct t0 ; try congruence.
      destruct t1.
      * (* int *)
        destruct t2 ; try congruence.
        destruct t  ; try congruence.
        apply T_If_Int.
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
        apply IHe3. reflexivity.
      * (* bool *)
        destruct t2 ; try congruence.
        destruct t  ; try congruence.
        apply T_If_Bool.
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
        apply IHe3. reflexivity.
    + (* concat *)
      intros.
      simpl in H.
      destruct (typeF e1) ; try congruence.
      destruct (typeF e2) ; try (destruct t0 ; congruence).
      destruct t0.
      * (* int *)
        destruct t1 ; try congruence.
        destruct t  ; try congruence.
        apply T_Concat_Int.
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
      * (* bool *)
        destruct t1 ; try congruence.
        destruct t  ; try congruence.
        apply T_Concat_Bool.
        apply IHe1. reflexivity.
        apply IHe2. reflexivity.
Qed.

Example typeR_1 :
  (EPlus (EInt 1) (EInt 2)) : intty.
Proof. apply typeR_eq_typeF. simpl. reflexivity. Qed.

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

Reserved Notation "e '~' m"
                  (at level 50, left associativity).

Inductive multR : expr -> mult -> Prop :=
  | M_Int : forall (n:nat),
      EInt n ~ one

  | M_True :
      ETrue ~ one

  | M_False :
      EFalse ~ one

  | M_Plus : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EPlus e1 e2 ~ mult_crossproduct m1 m2

  | M_Lt : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      ELt e1 e2 ~ mult_crossproduct m1 m2

  | M_If : forall (e1 e2 e3 : expr) m1 m2 m3,
      e1 ~ m1 ->
      e2 ~ m2 ->
      e3 ~ m3 ->
      EIf e1 e2 e3 ~ mult_crossproduct m1 (mult_crossproduct m2 m3)

  | M_Concat_Int : forall (e1 e2 : expr) m1 m2,
      e1 ~ m1 ->
      e2 ~ m2 ->
      EConcat e1 e2 ~ mult_concat m1 m2

where "e '~' m" := (multR e m) : type_scope.

Fixpoint multF (e : expr) : mult :=
  match e with
  | EInt n =>
      one

  | ETrue =>
      one

  | EFalse =>
      one

  | EPlus e1 e2 =>
      let m1 := multF e1 in
      let m2 := multF e2 in
      mult_crossproduct m1 m2

  | ELt e1 e2 =>
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

  end.

Theorem multR_eq_multF: forall e m,
  e ~ m <-> multF e = m.
Proof.
  split.
  - intros.
    induction H ;
    try (simpl ; subst ; reflexivity).
  - generalize dependent m.
    induction e ;
    intros ; simpl in H ; subst ; constructor ;
    try reflexivity ; (* literals *)
    try (apply IHe1 ; reflexivity);
    try (apply IHe2 ; reflexivity); (* binops *)
    try (apply IHe3 ; reflexivity). (* if *)
Qed.

Example multR_1 :
  (EPlus (EInt 1) (EInt 2)) ~ one.
Proof. apply multR_eq_multF. simpl. reflexivity. Qed.

Example multR_2 :
  (EConcat (EInt 1) (EInt 2)) ~ oneOrMore.
Proof. apply multR_eq_multF. simpl. reflexivity. Qed.


(***** valty : val -> type *****)
Definition valty (v : val) : type :=
  match v with
  | intv  _ => intty
  | boolv _ => boolty
  end.

(***** valmu : val -> mult *****)
Definition valmu (v : val) : mult :=
  match v with
  | intv  []        => zeroOrOne
  | intv  (_ :: []) => one
  | intv  (_ :: _ ) => oneOrMore
  | boolv []        => zeroOrOne
  | boolv (_ :: []) => one
  | boolv (_ :: _ ) => oneOrMore
  end.

Inductive mult_containsR: mult -> mult -> Prop :=
  | M_ZeroOrMore : forall m,
      mult_containsR zeroOrMore m
  | M_One : forall m,
      mult_containsR m one
  | M_Equal : forall m,
      mult_containsR m m
.

Definition mult_containsF (m1 : mult) (m2 : mult) : bool :=
  match m1, m2 with
  | zeroOrMore, _         => true
  | _         , one       => true
  | zeroOrOne , zeroOrOne => true
  | oneOrMore , oneOrMore => true
  | _         , _         => false
  end.

Theorem mult_containsR_eq_mult_containsF : forall (m1 m2 : mult),
  mult_containsR m1 m2 <-> mult_containsF m1 m2 = true.
Proof.
  split.
  - intros. induction H.
    + simpl. reflexivity.
    + simpl. destruct m ; simpl ; reflexivity.
    + destruct m ; simpl ; reflexivity.
  - intros.
    destruct m1 ; try inversion H ; destruct m2 ; try constructor ;
    try congruence.
Qed.

(***** type preservation *****)
Theorem type_preservation : forall (e : expr) t v,
  e : t ->
  e \\ v ->
  valty v = t.
Proof.
  intros e t v Htype Hval.
  induction Hval ;
  try ( simpl ; inversion Htype ; reflexivity ). (* literals, plus, lt *)
  - simpl. inversion Htype.
    + reflexivity.
    + subst. apply IHHval2 in H5. inversion H5.
  - simpl. inversion Htype.
    + subst. apply IHHval2 in H5. inversion H5.
    + reflexivity.
  - simpl. inversion Htype.
    + reflexivity.
    + subst. apply IHHval1 in H1. inversion H1.
  - simpl. inversion Htype.
    + subst. apply IHHval1 in H1. inversion H1.
    + reflexivity.
Qed.

(***** has type implies evaluates *****)
Theorem eval_type_totality : forall (e : expr) t,
  e : t ->
  exists v,
  e \\ v.
Proof.
  intros e t H.
  induction H.
  - exists (intv [n]). constructor.
  - exists (boolv [true]). constructor.
  - exists (boolv [false]). constructor.
  - destruct IHtypeR1. destruct IHtypeR2.
Abort.

Lemma exists_some: forall {X:Type} (v1:X),
  exists v2 : X,
    Some v1 =
    Some v2.
Proof.
  intros.
  exists v1.
  reflexivity.
Qed.

Theorem eval_type_totality' : forall (e : expr) t,
  e : t ->
  exists v,
  evalF e = Some v.
Proof.
  intros.
  induction H.
  - simpl. apply exists_some.
  - simpl. apply exists_some.
  - simpl. apply exists_some.
  - simpl.
    destruct IHtypeR1. destruct IHtypeR2.
    rewrite H1. rewrite H2.
    destruct x. destruct x0. (* use type preservation instead of destruct *)
    + apply exists_some.
    + apply evalR_eq_evalF in H2.
      apply type_preservation with (v:=boolv l0) in H0 ; try assumption.
      inversion H0.
    + apply evalR_eq_evalF in H1.
      apply type_preservation with (v:=boolv l) in H ; try assumption.
      inversion H.
  - simpl.
    destruct IHtypeR1. destruct IHtypeR2.
    rewrite H1. rewrite H2.
    destruct x. destruct x0.
    + apply exists_some.
    + apply evalR_eq_evalF in H2.
      apply type_preservation with (v:=boolv l0) in H0 ; try assumption.
      inversion H0.
    + apply evalR_eq_evalF in H1.
      apply type_preservation with (v:=boolv l) in H ; try assumption.
      inversion H.
  - simpl.
    destruct IHtypeR1. destruct IHtypeR2. destruct IHtypeR3.
    rewrite H2. rewrite H3. rewrite H4.
    destruct x. destruct x0. destruct x1.
    + apply evalR_eq_evalF in H2.
      apply type_preservation with (v:=intv l) in H ; try assumption.
      inversion H.
    + apply evalR_eq_evalF in H4.
      apply type_preservation with (v:=boolv l1) in H1 ; try assumption.
      inversion H1.
    + apply evalR_eq_evalF in H3.
      apply type_preservation with (v:=boolv l0) in H0 ; try assumption.
      inversion H0.
    + apply evalR_eq_evalF in H3.
      apply type_preservation with (v:=x0) in H0 ; try assumption.
      destruct x0 ; try inversion H0.
      apply evalR_eq_evalF in H4.
      apply type_preservation with (v:=x1) in H1 ; try assumption.
      destruct x1 ; try inversion H1.
      apply exists_some.
  - simpl.
    destruct IHtypeR1. destruct IHtypeR2. destruct IHtypeR3.
    rewrite H2. rewrite H3. rewrite H4.
    destruct x.
    { apply evalR_eq_evalF in H2.
      apply type_preservation with (v:=intv l) in H ; try assumption.
      inversion H. }
    destruct x0.
    { apply evalR_eq_evalF in H3.
      apply type_preservation with (v:=intv l0) in H0 ; try assumption.
      inversion H0. }
    destruct x1.
    { apply evalR_eq_evalF in H4.
      apply type_preservation with (v:=intv l1) in H1 ; try assumption.
      inversion H1. }
    + apply exists_some.
  - simpl.
    destruct IHtypeR1. destruct IHtypeR2.
    rewrite H1. rewrite H2.
    apply evalR_eq_evalF in H1.
    apply type_preservation with (v:=x) in H ; try assumption.
    destruct x ; try inversion H.
    apply evalR_eq_evalF in H2.
    apply type_preservation with (v:=x0) in H0 ; try assumption.
    destruct x0 ; try inversion H0.
    apply exists_some.
  - simpl.
    destruct IHtypeR1. destruct IHtypeR2.
    rewrite H1. rewrite H2.
    apply evalR_eq_evalF in H1.
    apply type_preservation with (v:=x) in H ; try assumption.
    destruct x ; try inversion H.
    apply evalR_eq_evalF in H2.
    apply type_preservation with (v:=x0) in H0 ; try assumption.
    destruct x0 ; try inversion H0.
    apply exists_some.
Qed.

(***** multiplicity preservation *****)
Theorem mult_preservation : forall (e : expr) t m v,
  e : t ->
  e ~ m ->
  e \\ v ->
  mult_containsR m (valmu v).
Proof.
  intros e t m v Htype Hmult Hval.
  generalize dependent t.
  generalize dependent m.
  induction Hval ;
  intros ;
  try (simpl ; constructor). (* literals *)
  - inversion Htype. subst.
    inversion Hmult. subst.
    specialize (IHHval1 m1).
    specialize (IHHval1 H1).
    specialize (IHHval1 intty).
    specialize (IHHval1 H2).
    specialize (IHHval2 m2).
    specialize (IHHval2 H5).
    specialize (IHHval2 intty).
    specialize (IHHval2 H4).

(* TODO: continue here *)

Abort.

