Require Import List.
Require Import String.

Require Import InvTactics.

(** Definitions of HTTP request **)

(* A line in an HTTP request can be:
     (1) Req_InitialMessage: the first line, for example "GET / HTTP/1.1".
     (2) Req_HeaderLine: a common header line delimited by a colon.
     (3) Req_BrokenLine: if a value in a Req_HeaderLine is too long,
                         it can be broken in to multiple lines.
                         This represents a broken line: in a well formed
                         request, it must follows a Req_HeaderLine.
 *)
Inductive HttpRequestLine : Type :=
| Req_InitialMessage : string -> HttpRequestLine
| Req_HeaderLine : string -> HttpRequestLine
| Req_BrokenLine : string -> HttpRequestLine.

Definition HttpRequest : Type := list HttpRequestLine.

(** What it means for an HTTP request to be well formed/complete. **)

(* The `well_formed_request` we defined here is kind of weak,
     it actually represents the remaining part of a well formed HTTP request
     header (its first several lines have been processed by the server.
 *)
Inductive well_formed_request: HttpRequest -> Prop :=
| wf_empty : well_formed_request nil
| wf_cons_header_line : forall s req, well_formed_request req ->
                                 well_formed_request ((Req_HeaderLine s) :: req)
| wf_cons_broken_line : forall s req, well_formed_request req ->
                                 well_formed_request ((Req_BrokenLine s) :: req).

(* A complete HTTP request must start with a `Req_InitialMessage`,
     followed by nothing or `Req_HeaderLine` and a list of request lines.
 *)
Inductive complete_request : HttpRequest -> Prop :=
| cr_only_initial: forall s,
    complete_request (Req_InitialMessage s :: nil)
| cr_start_with_initial: forall s1 s2 req,
    well_formed_request (Req_HeaderLine s1 :: req) ->
    complete_request (Req_InitialMessage s2 :: Req_HeaderLine s1 :: req).

(** Some theorems about well formed/complete HTTP requests. **)

Hint Constructors well_formed_request.

Lemma well_formed_request_inverse: forall line req,
    well_formed_request (line :: req) -> well_formed_request req.
Proof.
  intros. remember (line :: req) as req'.
  induction H; inversion Heqreq'; subst; auto.
Qed.

Lemma complete_request_not_empty : forall req,
    complete_request req -> req <> nil.
Proof.
  intros. intro. try solve by inversion 2.
Qed.

Lemma complete_request_inverse: forall line req,
    complete_request (line :: req) -> well_formed_request req.
Proof.
  intros. remember (line :: req) as req'.
  inversion H. subst. inversion H0. auto.
  subst. inversion H1. assumption.
Qed.

Lemma completet_request_starts_with_initial: forall r req,
    complete_request (r :: req) ->
    exists s, r = (Req_InitialMessage s).
Proof.
  intros. inversion H.
  - exists s. reflexivity.
  - exists s2. reflexivity.
Qed.

Lemma complete_request_has_initial_and_header_line: forall r req,
    req <> nil ->
    complete_request (r :: req) ->
    exists s req', req = (Req_HeaderLine s) :: req'.
Proof.
  intros. inversion H0; subst.
  - exfalso. apply H. reflexivity.
  - exists s1. exists req0. reflexivity.
Qed.
