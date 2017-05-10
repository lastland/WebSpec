Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.

Lemma substring_length : forall n size s,
    length (substring n size s) <= size.
Proof.
  intros. generalize dependent n. generalize dependent size.
  induction s; intros.
  - destruct size; destruct n; simpl; omega.
  - destruct size; induction n; simpl; try omega; eauto.
    apply le_n_S. auto.
Qed.

Fixpoint strcmp (a : string) (b : string) : bool :=
  match a with
  | EmptyString => match b with
          | EmptyString => true
          | _ => false
          end
  | String ca sa => match b with
                   | EmptyString => false
                   | String cb sb =>
                     andb (nat_of_ascii ca =? nat_of_ascii cb)
                          (strcmp sa sb)
                   end
  end.

Notation "x '<=?' y" := (leb x y)
  (at level 70, no associativity) : nat_scope.

Definition is_lower (c: ascii) : bool :=
  let n := nat_of_ascii c in
  (97 <=? n) && (n <=? 122).

Definition is_upper (c: ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90).

Definition to_lower (c: ascii) : ascii :=
  if is_upper c then
    ascii_of_nat ((nat_of_ascii c) + 32)
  else c.

Definition to_upper (c: ascii) : ascii :=
  if is_lower c then
    ascii_of_nat ((nat_of_ascii c) - 32)
  else c.

Require Import Coq.Lists.List.

Definition to_lower_word (s : list ascii) : list ascii :=
  map to_lower s.

Definition to_upper_word (s : list ascii) : list ascii :=
  map to_upper s.

Fixpoint reverse_string' (s s' : string) : string :=
  match s with
  | EmptyString => s'
  | String c s => reverse_string' s (String c s')
  end.

Definition reverse_string (s : string) : string :=
  reverse_string' s EmptyString.

(* Use n here as the ranking function to show that this terminates.
   Use (length l) should be enough. *)
Fixpoint bits_to_string (n: nat) (l: list bool) (s : string) : string :=
  match n with
  | O => s
  | S n' =>
    match l with
    | nil => reverse_string s
    | l => bits_to_string n' (skipn 8 l)
                         (String (ascii_of_N (N_of_digits (rev (firstn 8 l)))) s)
    end
  end.

Definition list_bits_to_string (l: list (list bool)) : string :=
  let l' := concat l in
  bits_to_string (length l') l' EmptyString.
