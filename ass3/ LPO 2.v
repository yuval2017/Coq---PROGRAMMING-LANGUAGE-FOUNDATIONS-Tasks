Set Implicit Arguments.
Unset Strict Implicit.
Require Import List Lia.
Definition semi_dec (P : nat -> Prop) :=
exists s : nat -> nat -> bool, forall x, P x <-> exists n, s x n =
true.

Definition dec (P : nat -> Prop) :=
exists d : nat -> bool, forall n, P n <-> d n = true.

Definition enum (P : nat -> Prop) :=
exists e : nat -> nat, forall x, P x <-> exists n, e n = x.


Definition LPO :=
forall f : nat -> bool, (exists n, f n = true) \/ (forall n, f n =
false).



(*------ Part 1 ------*)
Lemma Nat_eqb_refl : forall n : nat,
  Nat.eqb n n = true.
Proof.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive case: n = S n' *)
    simpl. apply IHn'.
Qed.

Lemma eqb_x_x_is_true : forall x : nat,
  Nat.eqb x x = true.
Proof.
  intros x.
  apply Nat_eqb_refl.
Qed.

Lemma Nat_eqb_eq : forall n m : nat,
  Nat.eqb n m = true -> n = m.
Proof.
  intros n m.
  revert n.
  induction m as [| m' IHm'].
  - (* Base case: m = 0 *)
    intros n H. destruct n as [| n'].
    + reflexivity.
    + simpl in H. discriminate.
  - (* Inductive case: m = S m' *)
    intros [| n'] H.
    + simpl in H. discriminate.
    + simpl in H. apply IHm' in H. f_equal. assumption.
Qed.

Lemma eqb_e_x_eq : forall (e : nat -> nat) (x0 x : nat),
  Nat.eqb (e x0) x = true -> e x0 = x.
Proof.
  intros e x0 x Heq.
  apply Nat_eqb_eq in Heq.
  assumption.
Qed.
Lemma enum_sdec (P : nat -> Prop) :
  enum P -> semi_dec P.
Proof.
  unfold enum, semi_dec. intros [e He].
  exists (fun x n => if Nat.eqb (e n) x then true else false).
  intros x.
  - firstorder. 
    +  apply He in H. destruct H as [n Hn]. destruct (Nat.eqb (e n) x) eqn:Heq.
      * exists n. rewrite Heq. reflexivity.
      * rewrite Hn in Heq. rewrite Nat_eqb_refl in Heq. discriminate.
    + destruct (Nat.eqb (e x0) x) eqn:Heq.
      * apply He. exists x0. apply eqb_e_x_eq. assumption.
      * lia.
Qed.
(**------------------**)





(*------ Part 3 ------*)
Definition halting_dec :=
exists F : (nat -> bool) -> bool, forall f, (exists n, f n = true) <-> F f = true.

Theorem halting_semi_dec P :
  halting_dec -> semi_dec P -> dec P.
Proof.
  unfold halting_dec, semi_dec, dec.
  intros [F HF] [s Hs].
  exists (fun n => F (fun x => s n x)).
  firstorder.
Qed.

(**------------------**)



Definition print (f : nat -> bool) (k : nat) : nat := if (f k) then 1 else 0.
  
Definition P_print (f : nat -> bool) := fun n => exists k, print f k = n.

Lemma true_iff_print_one : forall (f : nat -> bool) (k : nat),
  f k = true <-> print f k = 1.
Proof.
  intros f k.
  unfold print.
  destruct (f k) eqn:Hf.
  - (* f k = true *)
    split.
    + intros _. reflexivity.
    + intros _. reflexivity.
  - (* f k = false *)
    split.
    + intros H. discriminate H.
    + intros H. discriminate H.
Qed.
Theorem semi_dec_LPO (P : nat -> Prop) : (forall P, semi_dec P -> dec P) -> LPO.
Proof.
  unfold LPO.
  intros H f. 
  assert (semi_dec (fun n => f n = true)) as HQ_semi_dec.
  {
    exists (fun n k => if Nat.eqb k n then f n else false).
    intros n.
    split.
    - intros H1. exists n. rewrite eqb_x_x_is_true. assumption.
    - intros [k Hk].
       destruct (Nat.eqb k n) eqn:H1. 
      + assumption. 
      + discriminate.
  }
    right. intros n. destruct (H (fun n => f n = false)) as [d Hd]. 
    - apply enum_sdec. assumption.
    - destruct (d n) eqn:HdH.
      + exfalso. destruct (f n) eqn: HfH.
        * 
    
      + apply Hd in Hdn.
     destruct (H Q) as [d Hd].
    -  assumption. 
    - right. intros n. destruct (d n) eqn: Hdn.
      + apply Hd in Hdn.
    - left. unfold semi_dec in HQ_semi_dec. destruct HQ_semi_dec as [s Hs].
    +  

  

unfold semi_dec in H. destruct (H P) as [d Hd]. 
   - apply enum_sdec. unfold enum.
 exists (print f). reflexivity.
   - left. destruct (d (print f 1)) eqn:Heq.
      + destruct (Hd 1). lia. apply H1 in Heq. unfold P_print in Heq. destruct Heq as [k Hk].
        exists k. apply true_iff_print_one. assumption.
      + 







