Require Import Permutation.
Require Import List Arith.
Require Import Sorted.

Open Scope nat_scope.

Inductive perm: list nat -> list nat -> Prop :=
| perm_eq: forall l, perm l l
| perm_swap: forall x y l, perm (x :: y :: l) (y :: x :: l)
| perm_hd: forall x l l', perm l l' -> perm (x :: l) (x :: l')
| perm_trans: forall l l' l'', perm l l' -> perm l' l'' -> perm l l''.

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
Qed.

Fixpoint num_oc (x: nat) (l: list nat): nat :=
  match l with
  | nil => 0
  | h::tl => if (x =? h) then S (num_oc x tl) else num_oc x tl
end.

Definition equiv l l' := forall x, num_oc x l = num_oc x l'.

Lemma equiv_hd: forall l l' x, equiv l l' -> equiv (x :: l) (x :: l').
Proof.
  intros.
  unfold equiv in *.
  intro x0. simpl.
  destruct (x0 =? x).
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma equiv_nil: forall l, equiv nil l -> l = nil.
Proof.
  intro l. case l.
  - intro H. reflexivity.
  - intros.
    unfold equiv in H.
    specialize (H n). simpl in H.
    rewrite Nat.eqb_refl in H.
    inversion H.
Qed.

Lemma equiv_trans: forall l1 l2 l3, equiv l1 l2 -> equiv l2 l3 -> equiv l1 l3.
Proof.
  intros. induction l1. 
  - apply equiv_nil in H.
    rewrite H in H0. apply H0. 
  - unfold equiv in *. simpl in *.
    intro x.
    assert (H := H x).
    destruct (x =? a) in *.
    -- rewrite H. apply H0.
    -- rewrite H. apply H0.
Qed.

Lemma perm_list_comp: forall x n l, num_oc x l = S n -> exists l1 l2, l = l1++(x::l2).
Admitted.

Lemma perm_eq_conc: forall l1 l2 a, perm (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  induction l1.
  - intros. simpl. apply perm_eq.
  - intros. simpl.
    apply perm_trans with (a :: a0 :: l1 ++ l2).
    -- apply perm_swap.
    -- apply perm_hd. apply IHl1.
Qed.

Theorem perm_equiv: forall l l', equiv l l' <-> perm l l'.
Proof.
  split.
  (* -> 12 pontos *)
  - intro H. unfold equiv in H.
    generalize dependent l'.
    induction l.
    + intros l' H. simpl in *.
      apply equiv_nil in H. rewrite H. apply perm_eq.
    + intros l' H. simpl in H.
      generalize dependent l'.
      intros. specialize (H a).
      rewrite Nat.eqb_refl in H.
      symmetry in H.
      apply perm_list_comp in H.
      destruct H as [l1 H]; destruct H as [l2 H].
      rewrite H.
      apply perm_trans with (a :: l1 ++ l2).
      * apply perm_hd. apply IHl. admit.
      * apply perm_eq_conc.
      
      (* repenssando indução em l'
      intro l'. induction l'.
      * intro H. specialize (H a).
        rewrite <- beq_nat_refl in H.
        simpl in H.
        inversion H.
      * intro H. pose proof H.
        specialize (H0 a0).
        destruct (a0 =? a) eqn:Ha.
        ** symmetry in Ha.
           apply beq_nat_eq in Ha. subst.
           apply perm_hd. apply IHl. simpl in H.
           intro x. specialize (H x).
           destruct (x =? a).
           *** admit.
           *** admit.
        ** admit.*)
        
  (* <- 6 pontos *)
  - intro H. induction H.
    + unfold equiv. intro x. reflexivity.
    + apply equiv_trans with (y::x::l).
      * unfold equiv. intro x0. simpl.
         -- destruct (x0 =? x) eqn:H. destruct(x0 =? y) eqn:J.
            ** reflexivity.
            ** reflexivity.
            ** destruct(x0 =? y) eqn:J.
              --- reflexivity.
              --- reflexivity.
      * apply equiv_hd. apply equiv_hd.
        unfold equiv. intro x0. reflexivity.
    + apply equiv_hd. apply IHperm.
    + apply equiv_trans with l'.
      * apply IHperm1.
      * apply IHperm2.
Admitted.

