(*
This is an extension of multiplicities.v with expressions that use environments

Under construction
*)

Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Export Coq.FSets.FMapWeakList.
Require Export Coq.Structures.DecidableType.
Module StringEQ <: DecidableType.
  Definition t := string.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec := string_dec.
End StringEQ.
Module M := FMapWeakList.Make(StringEQ).

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

(***** Signatures *****)
Inductive expr : Type :=
  | EInt      : nat -> expr
  | ETrue     : expr
  | EFalse    : expr
  | EAnd      : expr -> expr -> expr
  | EPlus     : expr -> expr -> expr
  | EVar      : string -> expr
  | EFilter   : expr -> string -> expr -> expr.

Inductive val : Type :=
  | intv  : list nat -> val
  | boolv : list bool -> val.

Definition env: Type := M.t val.

(***** helper functions *****)
Definition get (m : env) (k : string) :=
  M.find k m.

Definition set (m : env) (k : string) (v : val) :=
  M.add k v m.

Definition empty :=
  M.empty nat.

(***** Interpreter *****)
Reserved Notation "env '|-' e '\\' v"
                  (at level 50, left associativity).

Inductive evalR : env -> expr -> val -> Prop :=
  | E_Int : forall env (n:nat),
      env |- EInt n \\ intv [n]

  | E_True : forall env,
      env |- ETrue \\ boolv [true]

  | E_False : forall env,
      env |- EFalse \\ boolv [false]

  | E_And : forall env (e1 e2 : expr) v1s v2s vtuples,
      env |- e1 \\ boolv v1s ->
      env |- e2 \\ boolv v2s ->
      vtuples = list_crossproduct v1s v2s ->
      env |- EAnd e1 e2 \\ boolv (map (funtuple andb) vtuples)

  | E_Plus : forall env (e1 e2 : expr) v1s v2s vtuples,
      env |- e1 \\ intv v1s ->
      env |- e2 \\ intv v2s -> 
      vtuples = list_crossproduct v1s v2s ->
      env |- EPlus e1 e2 \\ intv (map (funtuple plus) vtuples)

  | E_Var_Bool : forall env n v1s,
      Some (boolv v1s) = get env n ->
      env |- EVar n \\ boolv v1s

  (* add filter *)

where "env '|-' e '\\' v" := (evalR env e v) : type_scope.

Fixpoint evalF (env : env) (e : expr) : option val :=
  match e with
  | EInt n =>
      Some (intv [n])

  | ETrue =>
      Some (boolv [true])

  | EFalse =>
      Some (boolv [false])

  | EAnd e1 e2 =>
      let v1 := evalF env e1 in
      let v2 := evalF env e2 in
      match v1, v2 with
      | Some (boolv v1s), Some (boolv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple andb) vtuples in
          Some (boolv vs)
      | _,_ => None
      end

  | EPlus e1 e2 =>
      let v1 := evalF env e1 in
      let v2 := evalF env e2 in
      match v1, v2 with
      | Some (intv v1s), Some (intv v2s) =>
          let vtuples := list_crossproduct v1s v2s in
          let vs := map (funtuple plus) vtuples in
          Some (intv vs)
      | _,_ => None
      end

  | EVar n =>
      let v1 := get env n in
      v1

  | EFilter e1 n e2 => (* implement filter instead of lambda *)
      let v1 := evalF env e1 in
      match v1 with
      | Some (boolv v1s) =>
          let env' := set env n (boolv v1s) in (* use fold over elements *)
          let v2 := evalF env' e2 in
          v2
      | Some (intv v1s) =>
          let env' := set env n (intv v1s) in
          let v2 := evalF env' e2 in
          v2
      | None => None
      end
  end.
