Require Import List.
Require Import String.

Require Import Utility.
Require Import InvTactics.
Require Import HttpRequest.
Require Import HttpResponse.

(** What it means for an HTTP request and an HTTP response to be matched.
    Right now we only ask them both to be well formed. **)

Inductive request_response_matched (req: HttpRequest) (res: HttpResponse) : Prop :=
| wf_match: complete_request req ->
            well_formed_response res ->
            request_response_matched req res.

(** All the states of a connection. **)

Inductive State : Type :=
| Init 
| UrlReceived 
| HeaderPartReceived 
| HeadersReceived 
| HeadersProcessed
(* The behavior of the following states, until `FooterPartReceived`,
     have not been formalized yet. *)
| ContinueSending 
| ContinueSent 
| BodyReceived 
| FooterPartReceived
| FootersReceived 
| HeadersSending 
| HeadersSent 
| NormalBodyReady
| NormalBodyUnready
(* The behavior of the following states, until `FootersSent`,
     have not been formalized yet. *)
| ChunkedBodyReady
| ChunkedBodyUnready 
| BodySent
| FootersSending
| FootersSent
| Closed.

(** `has_state req1 req2 state res1 res2`
     means that it can happen that a connection at state `state`
     has processed `req2`, and has requests `req1` pending for processing,
     and it has sent `res2`, and has responses `res1` waiting to be sent.
     Right now, the part related to handling chunked data has not been
     modeled here yet. 
 **)
Inductive has_state : HttpRequest -> HttpRequest ->
                      State -> HttpResponse -> HttpResponse -> Prop :=
| S_Init: forall req,
    complete_request req ->
    has_state req nil Init nil nil
| S_InitClose: forall req,
    (* This is not exactly what happened in the web server,
     but this makes the proof easier. *)
    ~(complete_request (rev req)) ->
    has_state nil req Closed nil nil
| S_UrlReceived: forall s req,
    has_state (Req_InitialMessage s :: req) nil Init nil nil ->
    has_state req (Req_InitialMessage s :: nil) UrlReceived nil nil
| S_HeaderPartReceived1: forall req1 req2 req3 s,
    req1 = (Req_HeaderLine s) :: req2 ->
    has_state req1 req3 UrlReceived nil nil ->
    has_state req2 (Req_HeaderLine s :: req3) HeaderPartReceived nil nil
| S_HeaderPartReceived2: forall req1 req2 req3 line,
    req1 = line :: req2 ->
    has_state req1 req3 HeaderPartReceived nil nil ->
    has_state req2 (line :: req3) HeaderPartReceived nil nil
| S_HeadersReceived1: forall req,
    has_state nil (req :: nil) UrlReceived nil nil ->
    has_state nil (req :: nil) HeadersReceived nil nil
| S_HeadersReceived2: forall req,
    has_state nil req HeaderPartReceived nil nil ->
    has_state nil req HeadersReceived nil nil
| S_HeadersProcessed: forall req,
    has_state nil req HeadersReceived nil nil ->
    has_state nil req HeadersProcessed nil nil
| S_FootersReceived: forall req,
    has_state nil req HeadersProcessed nil nil ->
    has_state nil req FootersReceived nil nil
| S_HeadersSending1: forall req res,
    request_response_matched (rev req) res ->
    has_state nil req FootersReceived nil nil ->
    has_state nil req HeadersSending res nil
| S_HeaderSending2: forall req res1 res2 s,
    has_state nil req HeadersSending (Res_HeaderLine s :: res1) res2 ->
    has_state nil req HeadersSending res1 (Res_HeaderLine s :: res2)
| S_HeadersSent1: forall req res1 res2 s,
    has_state nil req HeadersSending (Res_BodyLine s :: res1) res2 ->
    has_state nil req HeadersSent (Res_BodyLine s :: res1) res2
| S_HeadersSent2: forall req res,
    has_state nil req HeadersSending nil res ->
    has_state nil req HeadersSent nil res
| S_NormalBodyUnready: forall req res1 res2,
    has_state nil req HeadersSent res1 res2 ->
    has_state nil req NormalBodyUnready res1 res2
| S_NormalBodyReady1: forall req res1 res2,
    has_state nil req NormalBodyUnready res1 res2 ->
    has_state nil req NormalBodyReady res1 res2
| S_NormalBodyReady2: forall req res1 res2 s,
    has_state nil req NormalBodyReady (Res_BodyLine s :: res1) res2 ->
    has_state nil req NormalBodyReady res1 (Res_BodyLine s :: res2)
| S_FootersSent: forall req res,
    has_state nil req NormalBodyReady nil res ->
    has_state nil req FootersSent nil res
| S_Closed: forall req res,
    has_state nil req FootersSent nil res ->
    has_state nil req Closed nil res.

(** Some theorems about the connection.
    The most import theorem (the last one), says that if a complete request
    was received, it would be answered with a matched response. 
 **)

Hint Resolve well_formed_request_inverse.
Hint Resolve complete_request_not_empty.
Hint Resolve complete_request_inverse.
Hint Resolve completet_request_starts_with_initial.
Hint Resolve complete_request_has_initial_and_header_line.
Hint Resolve well_formed_response_not_empty.

Hint Constructors has_state.

Lemma progress_req: forall r req1 req2 state res1 res2,
    has_state (r :: req1) req2 state res1 res2 ->
    exists state', has_state req1 (r :: req2) state' res1 res2.
Proof with eauto.
  intros. remember (r :: req1) as req0.
  assert (Hhs: has_state req0 req2 state res1 res2); auto.
  induction H; subst; try inversion Heqreq0...
  - apply completet_request_starts_with_initial in H.
    destruct H. subst. exists UrlReceived...
  - inversion H.
    apply complete_request_has_initial_and_header_line in H0. subst.
    destruct H0. destruct H0. inversion H0. subst.
    exists HeaderPartReceived. eapply S_HeaderPartReceived1.
    reflexivity. assumption.
    intro. inversion H2.
Qed.

Lemma req_relation: forall req1 req2 req3 state res1 res2,
    has_state (req1 ++ req2) req3 state res1 res2 ->
    exists state', has_state req2 (rev req1 ++ req3) state' res1 res2.
Proof.
  intros.
  generalize dependent state.
  generalize dependent req3.
  induction req1; intros.
  - simpl in *. exists state. assumption.
  - assert (exists state', has_state (req1 ++ req2) (a::req3) state' res1 res2).
    { eapply progress_req. apply H. }
    destruct H0. apply IHreq1 in H0.
    simpl. rewrite <- app_assoc. simpl. assumption. 
Qed.

Lemma progress_req_to_nil: forall req res1 res2,
    has_state req nil Init res1 res2 ->
    exists state, has_state nil (rev req) state res1 res2.
Proof.
  intros.
  assert (rev req ++ nil = rev req).
  { apply app_nil_r. }
  rewrite <- H0. eapply req_relation.
  rewrite app_nil_r. apply H.
Qed.

Lemma res_always_empty_or_well_formed : forall req1 req2 state res1 res2,
    has_state req1 req2 state res1 res2 ->
    well_formed_response (rev res2 ++ res1) \/ (rev res2 ++ res1 = nil).
Proof with auto.
  intros. induction H; simpl...
  - inversion H...
  - rewrite <- app_assoc. simpl...
  - rewrite <- app_assoc. simpl...
Qed.

Lemma progress_res : forall r req1 req2 state res1 res2,
    has_state req1 req2 state (r :: res1) res2 ->
    exists state', has_state req1 req2 state' res1 (r :: res2).
Proof with auto.
  intros. remember (r :: res1) as res0.
  assert (Hhs: has_state req1 req2 state res0 res2)...
         induction H; try inversion Heqres0; auto; subst.
  - destruct r.
    + exists HeadersSending...
    + exists NormalBodyReady...
  - destruct r.
    + exists HeadersSending...
    + exists NormalBodyReady...
  - exists NormalBodyReady...
  - destruct r.
    + apply res_always_empty_or_well_formed in Hhs.
      destruct Hhs.
      * exfalso. simpl in H1. rewrite <- app_assoc in H1. simpl in H1.
        eapply body_before_header_response_not_well_formed. apply H1.
      * simpl in H1. remember (rev res2 ++ Res_BodyLine s :: nil) as res'.
        exfalso. eapply nil_neq_app_cons. symmetry. apply H1.
    + exists NormalBodyReady...
Qed.

Lemma res_relation : forall req1 req2 state res1 res2 res3,
    has_state req1 req2 state (res1 ++ res2) res3 ->
    exists state', has_state req1 req2 state' res2 (rev res1 ++ res3).
Proof.
  intros.
  generalize dependent state.
  generalize dependent res3.
  induction res1; intros.
  - simpl in *. exists state. assumption.
  - assert (exists state', has_state req1 req2 state' (res1 ++ res2) (a::res3)).
    { eapply progress_res. apply H. }
    destruct H0. apply IHres1 in H0.
    simpl. rewrite <- app_assoc. simpl. apply H0.
Qed.

Lemma progress_res_to_nil : forall req res state,
    has_state nil req state res nil ->
    exists state', has_state nil req state' nil (rev res).
Proof.
  intros.
  assert (rev res = rev res ++ nil).
  { symmetry. apply app_nil_r. }
  rewrite H0. eapply res_relation.
  rewrite app_nil_r. apply H.
Qed.

Lemma close_after_finish : forall req res state,
    request_response_matched (rev req) (rev res) ->
    has_state nil req state nil res ->
    has_state nil req Closed nil res.
Proof.
  intros. remember nil as reqn. remember (@nil HttpResponseLine) as resn.
  assert (Hhs: has_state reqn req state resn res); auto.
  induction H0; subst; eauto; inversion H;
    try (repeat constructor; assumption);
    try (exfalso; eapply well_formed_response_not_empty; eauto).
Qed.

Lemma good_req_will_be_received : forall req,
    complete_request req ->
    has_state nil (rev req) FootersReceived nil nil.
Proof. 
  intros. assert (Hcr: complete_request req); auto.
  apply S_Init in H. 
  apply progress_req_to_nil in H. destruct H.
  induction x; inversion H; subst; eauto;
    try (rewrite rev_involutive in H0; contradiction);
    try (repeat constructor);
    solve [exfalso; eapply complete_request_not_empty; eauto
          | try solve by inversion 7].
Qed.

Theorem good_req_will_be_answered : forall req res,
    complete_request req ->
    request_response_matched req res ->
    has_state nil (rev req) Closed nil (rev res).
Proof.
  intros. apply good_req_will_be_received in H.
  apply S_HeadersSending1 with (res:=res) in H.
  apply progress_res_to_nil in H. destruct H.
  apply close_after_finish with (state:=x).
  rewrite rev_involutive. rewrite rev_involutive. assumption.
  assumption. rewrite rev_involutive. assumption.
Qed.
