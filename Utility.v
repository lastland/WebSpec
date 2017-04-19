Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.

Lemma nil_neq_app_cons : forall { A: Type } ( x : A ) l1 l2,
    nil <> l1 ++ x :: l2.
Proof.
  intros. induction l1; simpl; intro; inversion H.
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

Definition to_lower_word (s : list ascii) : list ascii :=
  map to_lower s.

Definition to_upper_word (s : list ascii) : list ascii :=
  map to_upper s.
