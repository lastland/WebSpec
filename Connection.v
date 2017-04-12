Require Import List.
Require Import String.

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" "4" :=
  solve_by_inversion_step (solve by inversion 3).
Tactic Notation "solve" "by" "inversion" "5" :=
  solve_by_inversion_step (solve by inversion 4).
Tactic Notation "solve" "by" "inversion" "6" :=
  solve_by_inversion_step (solve by inversion 5).
Tactic Notation "solve" "by" "inversion" "7" :=
  solve_by_inversion_step (solve by inversion 6).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

Module Connection.

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
  
  Hint Constructors well_formed_request.

  Lemma well_formed_request_inverse: forall line req,
      well_formed_request (line :: req) -> well_formed_request req.
  Proof.
    intros. remember (line :: req) as req'.
    induction H; inversion Heqreq'; subst; auto.
  Qed.

  (* A complete HTTP request must start with a `Req_InitialMessage`,
     followed by nothing or `Req_HeaderLine` and a list of request lines.
  *)
  Inductive complete_request : HttpRequest -> Prop :=
  | cr_only_initial: forall s,
      complete_request (Req_InitialMessage s :: nil)
  | cr_start_with_initial: forall s1 s2 req,
      well_formed_request (Req_HeaderLine s1 :: req) ->
      complete_request (Req_InitialMessage s2 :: Req_HeaderLine s1 :: req).

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

  Hint Resolve well_formed_request_inverse.
  Hint Resolve complete_request_not_empty.
  Hint Resolve complete_request_inverse.
  Hint Resolve completet_request_starts_with_initial.
  Hint Resolve complete_request_has_initial_and_header_line.

  Inductive HttpResponseLine : Type :=
  | Res_HeaderLine : string -> HttpResponseLine
  | Res_BodyLine : string -> HttpResponseLine.

  Definition HttpResponse : Type := list HttpResponseLine.

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

  Lemma nil_neq_app_cons : forall { A: Type } ( x : A ) l1 l2,
      nil <> l1 ++ x :: l2.
  Proof.
    intros. induction l1; simpl; intro; inversion H.
  Qed.

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

  Inductive request_response_matched (req: HttpRequest) (res: HttpResponse) : Prop :=
    | wf_match: complete_request req ->
                well_formed_response res ->
                request_response_matched req res.

  Lemma well_formed_response_not_empty : forall res,
      well_formed_response res ->
      res <> nil.
  Proof.
    intros. intro. inversion H; subst; inversion H2.
  Qed.

  Hint Resolve well_formed_response_not_empty.

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

  (* `has_state req1 req2 state res1 res2`
     means that it can happen that a connection at state `state`
     has processed `req2`, and has requests `req1` pending for processing,
     and it has sent `res2`, and has responses `res1` waiting to be sent.
     Right now, the part related to handling chunked data has not been
     modeled here yet. 
  *)
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
