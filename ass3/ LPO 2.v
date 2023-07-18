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


Require Import Classical_Prop.
Lemma f_n_is_false_forall : forall (n : nat) (f : nat -> bool), ~ (exists x : nat, f x = true) -> f n = false.
Proof.
  intros n f H_not_exists_true.
  destruct (f n) eqn:Heq_fn.
  - (* Case 1: f n = true *)
    exfalso.
    apply H_not_exists_true.
    exists n.
    assumption.
  - (* Case 2: f n = false *)
    reflexivity.
Qed.


Theorem semi_dec_LPO (P : nat -> Prop) : (forall P, semi_dec P -> dec P) -> LPO.
Proof.
  unfold LPO.
  intros H f.

  (* We will use LEM to split the cases for f n = true and f n = false *)
  destruct (classic (exists n, f n = true)) as [H_true | H_false].
  - (* Case 1: There exists an n such that f n = true *)
    left. assumption.

  - (* Case 2: For all n, f n = false *)
    right.
    intros n.

    (* We need to show that f n = false *)
    assert (f n = false) as H_false_n.
    {
      (* Suppose f n = true *)
      destruct (classic (f n = true)) as [H_case1 | H_case2].
      - (* Case 2.1: f n = true *)
        apply (f_n_is_false_forall n) in H_false. assumption.
      - (* Case 2.2: f n = false *)
        apply (f_n_is_false_forall n) in H_false. assumption.
    }
    assumption.
Qed.


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


