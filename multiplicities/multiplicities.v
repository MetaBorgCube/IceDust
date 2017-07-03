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
  | ENot    : expr -> expr
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

  | E_Not : forall (e1 : expr) v1s,
      e1 \\ boolv v1s ->
      ENot e1 \\ boolv (map negb v1s)

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

  | ENot e1 =>
      let v1 := evalF e1 in
      match v1 with
      | Some (boolv v1s) =>
          let vs := map negb v1s in
          Some (boolv vs)
      | _ => None
      end

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

  | T_Not : forall (e1 : expr),
      e1 : boolty ->
      ENot e1 : boolty

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

  | ENot e1 =>
      let t1 := typeF e1 in
      match t1 with
      | Some boolty =>
          Some boolty
      | _ => None
      end

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
    induction H.
    (* literals *)
    all: try(reflexivity).
    (* unops *)
    all: try rename IHtypeR into IHtypeR1.
    all: simpl.
    all: subst.
    all: rewrite IHtypeR1.
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
    all: constructor.
    all: try(apply IHe1; reflexivity).
    all: try(apply IHe2; reflexivity).
    all: try(apply IHe3; reflexivity).
Qed.

Example typeR_1 :
  (EPlus (EInt 1) (EInt 2)) : intty.
Proof. apply typeR_eq_typeF. simpl. reflexivity. Qed.

(***** multiplicity check : expr -> mult *****)
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

  | M_Not : forall (e1 : expr) m1,
      e1 ~ m1 ->
      ENot e1 ~ m1

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

  | ENot e1 =>
      let m1 := multF e1 in
      m1

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
    induction e.
    all: intros.
    all: simpl in H.
    all: subst.
    all: constructor.
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


(***** valty : val -> type *****)
Definition valty (v : val) : type :=
  match v with
  | intv  _ => intty
  | boolv _ => boolty
  end.

(***** valmu : val -> mult *****)
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
Ltac applyinv H1 H2 := apply H1 in H2; inversion H2.

Ltac find_applyinv1 :=
  match goal with
    H1: ?E1 : boolty -> valty (intv ?E2) = boolty,
    H2: ?E1 : boolty
    |- _ => applyinv H1 H2
  end.

Ltac find_applyinv2 :=
  match goal with
    H1: ?E1 : intty -> valty (boolv ?E2) = intty,
    H2: ?E1 : intty
    |- _ => applyinv H1 H2
  end.

Theorem type_preservation : forall (e : expr) t v,
  e : t ->
  e \\ v ->
  valty v = t.
Proof.
  intros e t v Htype Hval.
  induction Hval.
  (* happy path *)
  all: simpl ; inversion Htype ; try ( reflexivity ).
  (* wrong types *)
  all: subst.
  all: try(find_applyinv1).
  all: try(find_applyinv2).
Qed.

(***** has type implies evaluates *****)
Lemma exists_some: forall {X:Type} (v1:X),
  exists v2 : X,
    Some v1 =
    Some v2.
Proof.
  intros.
  exists v1.
  reflexivity.
Qed.

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
  all: destruct v1 ; try inversion H.
  all: try(apply exists_some).
  (* binops *)
  all: destruct IHtypeR2 as [v2 Hv2].
  all: rewrite Hv2.
  all: apply evalR_eq_evalF in Hv2.
  all: apply type_preservation with (v:=v2) in H0 ; try assumption.
  all: destruct v2 ; try inversion H0.
  all: try(apply exists_some).
  (* if *)
  all: destruct IHtypeR3 as [v3 Hv3].
  all: rewrite Hv3.
  all: apply evalR_eq_evalF in Hv3.
  all: apply type_preservation with (v:=v3) in H1 ; try assumption.
  all: destruct v3 ; try inversion H1.
  all: try(apply exists_some).
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
Lemma crossproduct_mult_preservation_nat_nat_nat:
  forall m1 m2 v1s v2s (f : nat * nat -> nat),
  mult_containsR m1 (intv v1s) ->
  mult_containsR m2 (intv v2s) ->
  mult_containsR
    (mult_crossproduct m1 m2)
    (intv (map f (list_crossproduct v1s v2s))).
Proof.
  intros.
  destruct m1; destruct m2.
  all : destruct v1s; try destruct v1s.
  all : destruct v2s; try destruct v2s.
  all : subst; simpl; try (constructor).
  all : try inversion H.
  all : try inversion H0.
Qed.

Lemma crossproduct_mult_preservation_nat_nat_bool:
  forall m1 m2 v1s v2s (f : nat * nat -> bool),
  mult_containsR m1 (intv v1s) ->
  mult_containsR m2 (intv v2s) ->
  mult_containsR
    (mult_crossproduct m1 m2)
    (boolv (map f (list_crossproduct v1s v2s))).
Proof.
  intros.
  destruct m1; destruct m2.
  all : destruct v1s; try destruct v1s.
  all : destruct v2s; try destruct v2s.
  all : subst; simpl; try (constructor).
  all : try inversion H.
  all : try inversion H0.
Qed.

Lemma concat_mult_preservation_nat:
  forall m1 m2 v1s v2s,
  mult_containsR m1 (intv v1s) ->
  mult_containsR m2 (intv v2s) ->
  mult_containsR
    (mult_concat m1 m2)
    (intv (v1s ++ v2s)).
Proof.
  intros.
  destruct m1; destruct m2.
  all : destruct v1s; try destruct v1s.
  all : destruct v2s; try destruct v2s.
  all : subst; simpl; try (constructor).
  all : try inversion H.
  all : try inversion H0.
Qed.

Lemma concat_mult_preservation_bool:
  forall m1 m2 v1s v2s,
  mult_containsR m1 (boolv v1s) ->
  mult_containsR m2 (boolv v2s) ->
  mult_containsR
    (mult_concat m1 m2)
    (boolv (v1s ++ v2s)).
Proof.
  intros.
  destruct m1; destruct m2.
  all : destruct v1s; try destruct v1s.
  all : destruct v2s; try destruct v2s.
  all : subst; simpl; try (constructor).
  all : try inversion H.
  all : try inversion H0.
Qed.

Lemma crossproduct_mult_preservation_bool_nat_nat_nat:
  forall m1 m2 m3 v1s v2s v3s (f : bool * (nat * nat) -> nat),
  mult_containsR m1 (boolv v1s) ->
  mult_containsR m2 (intv v2s) ->
  mult_containsR m3 (intv v3s) ->
  mult_containsR
    (mult_crossproduct m1 (mult_crossproduct m2 m3))
    (intv (map f (list_crossproduct v1s (list_crossproduct v2s v3s)))).
Proof.
  intros.
  destruct m1; destruct m2 ; destruct m3.
  all : destruct v1s; try destruct v1s.
  all : destruct v2s; try destruct v2s.
  all : destruct v3s; try destruct v3s.
  all : subst; simpl; try (constructor).
  all : try inversion H.
  all : try inversion H0.
  all : try inversion H1.
Qed.

Lemma crossproduct_mult_preservation_bool_bool_bool_bool:
  forall m1 m2 m3 v1s v2s v3s (f : bool * (bool * bool) -> bool),
  mult_containsR m1 (boolv v1s) ->
  mult_containsR m2 (boolv v2s) ->
  mult_containsR m3 (boolv v3s) ->
  mult_containsR
    (mult_crossproduct m1 (mult_crossproduct m2 m3))
    (boolv (map f (list_crossproduct v1s (list_crossproduct v2s v3s)))).
Proof.
  intros.
  destruct m1; destruct m2 ; destruct m3.
  all : destruct v1s; try destruct v1s.
  all : destruct v2s; try destruct v2s.
  all : destruct v3s; try destruct v3s.
  all : subst; simpl; try (constructor).
  all : try inversion H.
  all : try inversion H0.
  all : try inversion H1.
Qed.

Lemma map_mult_preservation_bool_bool:
  forall m1 v1s (f : bool -> bool),
  mult_containsR m1 (boolv v1s) ->
  mult_containsR
    m1
    (boolv (map f v1s)).
Proof.
  intros.
  destruct m1.
  all : destruct v1s; try destruct v1s.
  all : subst; simpl; try (constructor).
  all : try inversion H.
Qed.

Ltac rename_He1ty e1 :=
  match goal with
    H1 : e1 : ?E
    |- _ => rename H1 into He1ty
  end.
Ltac rename_He2ty e2 :=
  match goal with
    H1 : e2 : ?E
    |- _ => rename H1 into He2ty
  end.
Ltac rename_He3ty e3 :=
  match goal with
    H1 : e3 : ?E
    |- _ => rename H1 into He3ty
  end.
Ltac rename_He1mu e1 :=
  match goal with
    H1 : e1 ~ ?E
    |- _ => rename H1 into He1mu
  end.
Ltac rename_He2mu e2 :=
  match goal with
    H1 : e2 ~ ?E
    |- _ => rename H1 into He2mu
  end.
Ltac rename_He3mu e3 :=
  match goal with
    H1 : e3 ~ ?E
    |- _ => rename H1 into He3mu
  end.

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

Ltac wrong_argument_types_1 :=
  match goal with
    H1 : ?E2 \\ intv ?V,
    H2 : ?E2 : boolty
    |- _ => 
    apply type_preservation with (v:=intv V) in H2;
    try assumption;
    inversion H2
  end.
Ltac wrong_argument_types_2 :=
  match goal with
    H1 : ?E2 \\ boolv ?V,
    H2 : ?E2 : intty
    |- _ => 
    apply type_preservation with (v:=boolv V) in H2;
    try assumption;
    inversion H2
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
  (* literals *)
  all: try(simpl; constructor).
  (* binops and if *)
  all: inversion Htype.
  all: subst.
  (* get rid of wrong argument type cases *)
  all: try wrong_argument_types_1.
  all: try wrong_argument_types_2.
  (* happy path *)
  all: inversion Hmult.
  all: subst.
  all: rename_He1ty e1.
  all: try(rename_He2ty e2).
  all: try(rename_He3ty e3).
  all: rename_He1mu e1.
  all: try(rename_He2mu e2).
  all: try(rename_He3mu e3).
  all: try rename m into m1.
  all: try rename IHHval into IHHval1.
  all: specialize (IHHval1 m1).
  all: specialize (IHHval1 He1mu).
  all: try(specialize (IHHval2 m2)).
  all: try(specialize (IHHval2 He2mu)).
  all: try(specialize (IHHval3 m3)).
  all: try(specialize (IHHval3 He3mu)).
  all: repeat(specialize_int).
  all: repeat(specialize_bool).
  all: specialize (IHHval1 He1ty).
  all: try(specialize (IHHval2 He2ty)).
  all: try(specialize (IHHval3 He3ty)).
  - apply map_mult_preservation_bool_bool;
    assumption.
  - apply crossproduct_mult_preservation_nat_nat_nat;
    assumption.
  - apply crossproduct_mult_preservation_nat_nat_bool;
    assumption.
  - apply crossproduct_mult_preservation_bool_nat_nat_nat;
    assumption.
  - apply crossproduct_mult_preservation_bool_bool_bool_bool;
    assumption.
  - apply concat_mult_preservation_nat;
    assumption.
  - apply concat_mult_preservation_bool;
    assumption.
Qed.

