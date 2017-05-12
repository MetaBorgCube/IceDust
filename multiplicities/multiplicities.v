Inductive expr : Type :=
  | intl : nat -> expr
  | plus : expr -> expr -> expr.

Inductive val : Type :=
  | intv : nat -> val.

Fixpoint eval (b : expr) : val :=
  match b with
  | intl n => intv n
  | plus e1 e2 =>
      let v1 := eval e1 in
      let v2 := eval e2 in
      match v1, v2 with
      | intv n1, intv n2 => intv (n1 + n2)
      end
  end.

Example test_bin_incr1 :
eval (plus (intl 1) (intl 2)) = intv 3.
Proof. simpl. reflexivity.
Qed.

(*
Fixpoint cross_product
(v1s : list val) (v2s : list val) : Vector 2 val :=
  v1s.

Fixpoint eval2 (b : expr) : list val :=
  match b with
  | intl n => cons (intv n) nil
  | plus e1 e2 =>
      let v1 := eval2 e1 in
      let v2 := eval2 e2 in
      match v1, v2 with
      | intv n1, intv n2 => intv (n1 + n2)
      end
  end.
*)