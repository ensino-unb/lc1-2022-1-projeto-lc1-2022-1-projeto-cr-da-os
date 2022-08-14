(** * Projeto de LC1 - 2022-1 (30 pontos)  *)

(** ** Introdução  *)
(** Esta é a introdução ... *)

(* begin hide *)
Require Import List Arith.

Open Scope nat_scope.

Require Import Sorted.
(* end hide *)
Print nat.
Print nat_ind.
Check nat_ind.

Inductive sorted : list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_one: forall x, sorted (x :: nil)
| sorted_all: forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Check sorted_ind.

Inductive perm : list nat -> list nat -> Prop :=
| perm_eq: forall l, perm l l
| perm_swap: forall x y l, perm (x :: y :: l) (y :: x :: l)
| perm_hd: forall x l l', perm l l' -> perm (x :: l) (x :: l')
| perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Check perm_ind.

Require Import Permutation.

Print Permutation.
Check Permutation_ind.

(** (2 pontos) *)
Lemma perm_equiv_Permutation: forall l1 l2, perm l1 l2 <-> Permutation l1 l2.
Proof.
Admitted.

Fixpoint num_oc (x: nat) (l: list nat): nat :=
  match l with
  | nil => 0
  | h::tl => if (x =? h) then S (num_oc x tl) else num_oc x tl
end.

Eval compute in (num_oc 2 (2::3::2::nil)).

Definition equiv l l' := forall x, num_oc x l = num_oc x l'.

(** (18 pontos) *)
Theorem perm_equiv: forall l l', equiv l l' <-> perm l l'.
Proof.
  split.
  (* -> 12 pontos *)
  - admit.
  (* <- 6 pontos *)
  - intro H. induction H.
    -- unfold equiv. intro x. reflexivity.
    -- unfold equiv. admit.
    -- unfold equiv in *. intro x'. simpl.
       destruct (x' =? x) eqn:H'.
       --- admit.
       --- admit.
    -- Admitted.

(* ou (exclusivo) *)
Theorem Permutation_equiv: forall l l', equiv l l' <-> Permutation l l'.
Proof.
  Admitted.

(** Bubblesort *)
Require Import Recdef.

Function bubble (l: list nat) {measure length} :=
  match l with
  | h1 :: h2 :: tl =>
    if h1 <=? h2
    then  h1 :: (bubble (h2 :: tl))
    else h2 :: (bubble (h1 :: tl))
    | _ => l
  end.
(* begin hide *)
Proof.
  - intros.
    simpl.
    apply Nat.lt_succ_diag_r.
  - intros.
    simpl.
    apply Nat.lt_succ_diag_r.
Defined.
(* end hide *)

Lemma bubble_sorted: forall l, sorted l -> bubble l = l.
Proof.
    Admitted. 

Fixpoint bubblesort (l: list nat) :=
  match l with
  | nil => l
  | h::tl => bubble (h :: bubblesort tl)
  end.

(*
bubblesort (3::2::1::nil) = 
bubble (3::bubblesort(2::1::nil)) = 
bubble (3::bubble(2::bubblesort(1::nil))) = 
bubble (3::bubble(2::bubble(1::bubblesort(nil)))) = 
bubble (3::bubble(2::1::nil)) = 
bubble (3::1::bubble(2::nil)) = 
bubble (3::1::2::nil) = 
1::bubble (3::2::nil) = 
1::2::bubble (3::nil) = 
1::2::3::nil = 
 *)

(* 10 pontos *)
Theorem bubblesort_sorts: forall l, sorted (bubblesort l).
Proof.
Admitted.

(* 10 pontos *)
Theorem bubblesort_perm: forall l, perm l (bubblesort l).
Proof.
Admitted.

(* ou exclusivo *)
Theorem bubblesort_Permutation: forall l, Permutation l (bubblesort l).
Proof.
Admitted.

(* ou *)
Theorem bubblesort_equiv: forall l, equiv l (bubblesort l).
Proof.
Admitted.
