Require Import Coq.Lists.List.

Lemma nil_neq_app_cons : forall { A: Type } ( x : A ) l1 l2,
    nil <> l1 ++ x :: l2.
Proof.
  intros. induction l1; simpl; intro; inversion H.
Qed.
