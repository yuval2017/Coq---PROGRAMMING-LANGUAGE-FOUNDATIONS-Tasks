From LF Require Export Poly.


(* Please red this: 
The Proofs are: drop_rev_length, drop_n_after_cons, 
in addition to prove drop_rev_length i used lemma's that i did proofed.
*)

Fixpoint drop {A: Type} (n m: nat) (l: list A) : list A :=
    match l with
    | [] => []
    | x :: rest_l =>
        match n, m with
        | O, _ => []
        | S n', O => x:: drop n' 0 rest_l  
        | _, S m'=> drop n m' rest_l
        end
    end.

Example test_drop2: drop 3 2 [7; 8; 20; 2; 11; 15; 6] = [20; 2; 11].
    Proof. simpl. reflexivity. Qed.

Example test_drop3: drop 0 2 [7; 8; 20; 2; 11; 15; 6] = [].
    Proof. simpl. reflexivity. Qed.

  Example test_drop_drop_all_elements: drop 5 0 [1; 2; 3; 4; 5] = [1; 2; 3; 4; 5].
  Proof. simpl. reflexivity. Qed.

  Example test_drop4: drop 10 2 [7; 8; 20; 2; 11; 15; 6] = [20; 2; 11; 15; 6].
  Proof. simpl. reflexivity. Qed.

  Example test_drop5: drop 1 7 [7; 8; 20; 2; 11; 15; 6] = [].
  Proof. simpl. reflexivity. Qed.

  (*the proofs is after the two lemma's*)

  (* lemma for the proofs*)
  Lemma rev_length : forall (A: Type) (l : list A),
  length (rev l) = length l.
  Proof.
  intros A l. induction l as [| x l' IHl'].
  - reflexivity. (* l = nil *)
  - simpl. rewrite -> app_length. (* l = cons *)
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity.
Qed.
(* lemma for the proofs*)
Lemma help_lemma : forall (A: Type) (l : list A),
  length l + 1 = S (length l).
Proof.
  intros A l.
  induction l as [| x l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

(*proof 1*)
Theorem drop_rev_length : forall (A: Type) (n m: nat) (lst: list A),
    length (rev (drop n m lst)) = length (drop n m lst).
Proof.
  intros A n m lst.
  destruct lst.
  - simpl. reflexivity.
  - destruct n as [| n'] eqn:E.
   + simpl. reflexivity.
   + destruct m as [| m'] eqn:D.
    * simpl. rewrite -> app_length with (l1 := rev (drop n' 0 lst)) (l2 := [x]).
            simpl. rewrite rev_length. rewrite help_lemma. reflexivity.
    * simpl. rewrite -> rev_length. reflexivity.
Qed.


(*proof 2*)
Theorem drop_n_after_cons : forall (A: Type) (n m : nat) (x: A) (lst: list A),
  m = n -> drop n (S m) (x :: lst) = drop n m lst.
Proof.
  intros A n m x lst H.
  rewrite H. 
  destruct n.
  - destruct lst as [|y lst'] eqn:E.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct lst as [| y lst'] eqn:E.
    + simpl. reflexivity. 
    + simpl. reflexivity.
Qed.


