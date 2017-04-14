Require Import List.
Require Import String.

Require Import InvTactics.
Require Import Utility.

(** Definitions of HTTP response. **)

Inductive HttpResponsePart : Type :=
| Res_HeaderPart : string -> HttpResponsePart
| Res_BodyPart : string -> HttpResponsePart.

Definition HttpResponse : Type := list HttpResponsePart.

(** Definitions of what a well formed HTTP response is. *)

Inductive response_body : HttpResponse -> Prop :=
| rb_cons_nil : forall s,
    response_body (Res_BodyPart s :: nil)
| rb_cons_body : forall s res,
    response_body res ->
    response_body (Res_BodyPart s :: res).

Inductive response_header : HttpResponse -> Prop :=
| rf_cons_body : forall s res,
    response_body res ->
    response_header (Res_HeaderPart s :: res)
| rf_cons_header : forall s res,
    response_header res ->
    response_header (Res_HeaderPart s :: res).

Hint Constructors response_body.
Hint Constructors response_header.

(* A well formed response must be some header lines followed by some body lines.
     That means, header lines can not be between body lines,
     or the other way around. 
 *)
Definition well_formed_response (res: HttpResponse) : Prop := response_header res.

(** The same definitions as above, but defined in functions. **)

Definition is_response_body (res: HttpResponsePart) : bool :=
  match res with
  | Res_BodyPart _ => true
  | _ => false
  end.

Definition has_only_response_body (res: HttpResponse) : bool :=
  forallb is_response_body res.

Fixpoint is_well_formed_response_rec (res: HttpResponse) : bool :=
  match res with
  | Res_HeaderPart _ :: rs => is_well_formed_response_rec rs
  | Res_BodyPart _ :: rs => has_only_response_body rs
  | _ => false
  end.

Definition is_well_formed_response (res: HttpResponse) : bool :=
  match res with
  | Res_HeaderPart _ :: rs => is_well_formed_response_rec rs
  | _ => false
  end.

(** Some theorems about well formed HTTP response. **)

Lemma response_body_no_header_line:
  forall res1 res2 s,
    ~ response_body (res1 ++ Res_HeaderPart s :: res2).
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
                                 Res_BodyPart s1 :: Res_HeaderPart s2 :: res2).
Proof.
  intros. induction res1; simpl; intro.
  - inversion H.
  - inversion H; subst.
    + assert (response_body ((res1 ++ Res_BodyPart s1 :: nil) ++ (Res_HeaderPart s2 :: res2))).
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

(** Proof that our inductive definitions and function definitions are equivalent.
 **)

Lemma response_body_has_only_response_body : forall res,
    response_body res -> has_only_response_body res = true.
Proof.
  intros res H. induction H; auto.
Qed.

Lemma has_only_response_body_add_body_is_response_body : forall s res,
    has_only_response_body res = true -> response_body (Res_BodyPart s :: res).
Proof.
  intros s res H. generalize dependent s.
  induction res; auto.
  - intros s. apply rb_cons_body. destruct a.
    + simpl in H. inversion H.
    + apply IHres. rewrite <- H. auto.
Qed.

Lemma response_body_implies_is_well_formed_response_rec : forall res,
    response_body res -> is_well_formed_response_rec res = true.
Proof.
  intros res H. induction H; auto.
  - simpl. apply response_body_has_only_response_body; assumption.
Qed.

Lemma response_header_implies_is_well_formed_response_rec : forall res,
    response_header res -> is_well_formed_response_rec res = true.
Proof.
  intros res H. induction H; simpl.
  - apply response_body_implies_is_well_formed_response_rec; assumption.
  - assumption.
Qed.

Theorem well_formed_response_is_well_formed_response : forall res,
    well_formed_response res <-> is_well_formed_response res = true.
Proof.
  intro res. induction res as [| r rs].
  - simpl; split; intros; try solve by inversion.
  - destruct r; split; intro H; try solve by inversion.
    + inversion H; subst; simpl.
      * apply response_body_implies_is_well_formed_response_rec.
        assumption.
      * apply response_header_implies_is_well_formed_response_rec.
        assumption.
    + destruct rs as [| r' rs'].
      * simpl in H. inversion H.
      * destruct r'.
        { apply rf_cons_header. apply IHrs.
          simpl in *. assumption. }
        { apply rf_cons_body.
          apply has_only_response_body_add_body_is_response_body.
          simpl in H. assumption. }
Qed.
