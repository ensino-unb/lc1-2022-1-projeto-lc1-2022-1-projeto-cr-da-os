Require Import Permutation.
Require Import List Arith.
Require Import Sorted.

Open Scope nat_scope.

Inductive perm: list nat -> list nat -> Prop :=
| perm_eq: forall l, perm l l
| perm_swap: forall x y l, perm (x :: y :: l) (y :: x :: l)
| perm_hd: forall x l l', perm l l' -> perm (x :: l) (x :: l')
| perm_trans: forall l l' l'', perm l l' -> perm l' l'' -> perm l' l'' -> perm l l''.

Lemma perm_equiv_Permutation: forall l1 l2, perm l1 l2 <-> Permutation l1 l2.

(* prova: 2 pontos *)
Proof.
  split.
  - intro H. induction H.
    -- apply Permutation_refl.
    -- apply Permutation.perm_swap.
    -- apply Permutation.perm_skip.
      --- apply IHperm.
    -- apply Permutation.perm_trans with (l').
      --- apply IHperm1.
      --- apply IHperm2.
  - intro H. induction H.
    -- apply perm_eq.
    -- apply perm_hd.
      --- apply IHPermutation.
    -- apply perm_swap.
    -- apply perm_trans with (l').
      --- apply IHPermutation1.
      --- apply IHPermutation2.
      --- apply IHPermutation2.
Qed.

Fixpoint num_oc (x: nat) (l: list nat): nat :=
  match l with
  | nil => 0
  | h::tl => if (x =? h) then S (num_oc x tl) else num_oc x tl
end.

Eval compute in (num_oc 2 (2::3::2::nil)).

Definition equiv l l' := forall x, num_oc x l = num_oc x l'.

Theorem perm_equiv: forall l l', equiv l l' <-> perm l l'.
Proof.
  split.
  (* -> 12 pontos *)
  - admit.
  (* <- 6 pontos *)
  - intro H. induction H.
    -- unfold equiv. intro x. reflexivity.
    -- unfold equiv. intro x0. simpl.
      destruct (x0 =? x).
      --- destruct (x0 =? y).
        ---- reflexivity.
        ---- reflexivity. 
      --- destruct (x0 =? y).
        ---- reflexivity.
        ---- reflexivity.
    -- unfold equiv in *. intro x'. simpl.
      destruct (x' =? x) eqn:H'.
      --- rewrite IHperm. reflexivity.
      --- rewrite IHperm. reflexivity.
    -- unfold equiv in *. intro x.
      --- admit.
Qed.

(* ou (exclusivo) *)
Theorem Permutation_equiv: forall l l', equiv l l' <-> Permutation l l'.
Proof.
  Admitted.
