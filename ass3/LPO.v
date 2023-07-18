Set Implicit Arguments.
Unset Strict Implicit.
Require Import List Lia.

Definition enum_mono (P : nat -> Prop) :=
exists e : nat -> nat, (forall k k', k <= k' -> e k <= e k') /\ forall
n, P n <-> exists k, e k = n.

Definition dec (P : nat -> Prop) :=
exists d : nat -> bool, forall n, P n <-> d n = true.


Definition LPO :=
forall f : nat -> bool, (exists n, f n = true) \/ (forall n, f n =
false).

Definition print (f : nat -> bool) (k : nat) : nat :=
  let lst := filter (fun n => if f n then true else false) (seq 0 (S k)) in
  length lst.
Lemma filter_incl : forall (l1 l2 : list nat) (f : nat -> bool),
  incl l1 l2 -> incl (filter f l1) (filter f l2).
Proof.
  intros l1 l2 f H_incl x H_in.
  apply filter_In in H_in.
  destruct H_in as [H_in_l1 H_f].
  apply filter_In.
  split.
  - apply H_incl. assumption.
  - assumption.
Qed.
Lemma le_trans : forall n m p : nat, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p H1 H2. induction H2.
  - (* Base case: m = p *)
    assumption.
  - (* Inductive case: m <= S p *)
    apply le_S. assumption.
Qed.
Lemma le_0_l : forall n : nat, 0 <= n.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    apply le_n.
  - (* n = S n' *)
    apply le_S.
    apply IHn'.
Qed.
Lemma incl_length_le : forall (l1 l2 : list nat),
  incl l1 l2 -> length l1 <= length l2.
Proof.
 
Admitted.
Lemma filter_subset_length : forall (l1 l2 : list nat) (f : nat -> bool),
  incl l1 l2 -> length (filter f l1) <= length (filter f l2).
Proof.
  intros l1 l2 f H_incl.
  assert (H1: incl (filter f l1) (filter f l2)).
  - apply filter_incl. assumption.
  - apply incl_length_le. assumption.
Qed.

Lemma incl_seq : forall k k',
  k <= k' -> incl (seq 0 (S k)) (seq 0 (S k')).
Proof.
  intros k k' H.
  intros x Hx.
  apply in_seq in Hx.
  apply in_seq.
  split.
  - lia.
  - lia.
Qed.
Lemma print_mono : forall f k k',
  k <= k' -> print f k <= print f k'.
Proof.
  intros f k k' H.
  unfold print.
  assert (inc: incl (seq 0 (S k)) (seq 0 (S k'))).
  - apply incl_seq. assumption.
  - apply filter_subset_length. assumption.
Qed.

Definition P_print (f : nat -> bool) := fun n => exists k, print f k = n.



Lemma P_print_iff : forall f n,
  P_print f n <-> exists k, print f k = n.
Proof.
  intros f n.
  unfold P_print.
  reflexivity.
Qed.

Lemma not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b.
  - contradiction.
  - reflexivity. 
Qed.
Lemma print_f_0 : forall (f: nat -> bool) (n k: nat), 
  print f k = n -> n <= k.
  Proof.
  Admitted.
Lemma print_le_0 : forall (f: nat -> bool) (k: nat), 
  print f k <= 0.
  Proof.
  Admitted.
Theorem enum_mono_dec_LPO :
(forall P, enum_mono P -> dec P) -> LPO.
Proof.
intros H f. destruct (H (P_print f)) as [d Hd].
- exists (print f). split; try apply print_mono. reflexivity. 
- left. destruct (Hd 0). unfold P_print in Hd.
  


