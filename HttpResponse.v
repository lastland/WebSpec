Require Import List.
Require Import String.

Require Import Utility.

(** Definitions of HTTP response. **)

Inductive HttpResponseLine : Type :=
| Res_HeaderLine : string -> HttpResponseLine
| Res_BodyLine : string -> HttpResponseLine.

Definition HttpResponse : Type := list HttpResponseLine.

(** Definitions of what a well formed HTTP response is. *)

Inductive response_body : HttpResponse -> Prop :=
| rb_cons_nil : forall s,
    response_body (Res_BodyLine s :: nil)
| rb_cons_body : forall s res,
    response_body res ->
    response_body (Res_BodyLine s :: res).

Inductive response_header : HttpResponse -> Prop :=
| rf_cons_body : forall s res,
    response_body res ->
    response_header (Res_HeaderLine s :: res)
| rf_cons_header : forall s res,
    response_header res ->
    response_header (Res_HeaderLine s :: res).

(* A well formed response must be some header lines followed by some body lines.
     That means, header lines can not be between body lines,
     or the other way around. 
 *)
Definition well_formed_response (res: HttpResponse) : Prop := response_header res.

(** Some theorems about well formed HTTP response. **)

Lemma response_body_no_header_line:
  forall res1 res2 s,
    ~ response_body (res1 ++ Res_HeaderLine s :: res2).
Proof.
  intros. induction res1; simpl; intro.
  - inversion H.
  - destruct a.
    + inversion H.
    + inversion H.
      * eapply nil_neq_app_cons. apply H2.
      * contradiction.
Qed.

Lemma body_before_header_response_not_well_formed:
  forall res1 res2 s1 s2,
    ~ well_formed_response (res1 ++
                                 Res_BodyLine s1 :: Res_HeaderLine s2 :: res2).
Proof.
  intros. induction res1; simpl; intro.
  - inversion H.
  - inversion H; subst.
    + assert (response_body ((res1 ++ Res_BodyLine s1 :: nil) ++ (Res_HeaderLine s2 :: res2))).
      { rewrite <- app_assoc. simpl. assumption. }
      eapply response_body_no_header_line. apply H0.
    + unfold well_formed_response in IHres1. contradiction.
Qed.

Lemma well_formed_response_not_empty : forall res,
    well_formed_response res ->
    res <> nil.
Proof.
  intros. intro. inversion H; subst; inversion H2.
Qed.
