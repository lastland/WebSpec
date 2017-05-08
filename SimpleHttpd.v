Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.


Require Import Buffer.
Require Import StringUtility.
Require Import Resource.
Require Import HttpdInterface.

Module SimpleHttpd (res: Resource) : Httpd (res).
  Definition RS ( A : Type ) := res.resource -> (A * res.resource).

  (** Callbacks. **)
  Definition contentReaderCallback : Type :=
    res.class -> nat -> nat -> buffer (RS bool).

  Definition contentReaderFreeCallback : Type :=
    res.class -> RS unit.

  (** Data types. **)
  Record _response := mkRes {
                          content : option string;
                          crc : option contentReaderCallback;
                          crfc : option contentReaderFreeCallback;
                          crc_cls : option res.resource
                        }.
  
  Definition connection : Type := nat.
  Definition response : Type := _response.
  Definition daemon : Type := list (connection * nat * response).
  Definition DM ( A : Type ) := daemon -> (A * daemon).

  (** Httpd interfaces. **)
  Definition create_response_from_buffer (size: nat) (mode: responseMemoryMode) :
    buffer (DM (option response)) :=
    fun buf => ((fun d => (Some (mkRes (Some (substring 0 size buf)) None None None),
                     d)), buf).

  Definition create_response_from_callback (size: nat) (blk_size: nat)
             (crc: contentReaderCallback) (r: res.resource)
             (crfc: contentReaderFreeCallback) : DM (option response) :=
    fun d => (Some (mkRes None (Some crc) (Some crfc) (Some r)), d).

  Definition queue_response (conn: connection) (code: nat) (res: response) : DM bool :=
    fun d => (true, (conn, code, res) :: d).

  Hint Unfold create_response_from_buffer.
  Hint Unfold create_response_from_callback.
  Hint Unfold queue_response.

  (** Abstract States. **)
  Definition response_queue (d: daemon) : list (connection * nat * response) := d.
  Definition response_content (r: response) : option string := content r.
  Definition response_crc (r: response) :
    option contentReaderCallback := crc r.
  Definition response_crfc (r: response) :
    option contentReaderFreeCallback := crfc r.
  Definition response_crc_cls (r: response) :
    option res.resource := crc_cls r.

  Hint Unfold response_queue.
  Hint Unfold response_content.
  Hint Unfold response_crc.
  Hint Unfold response_crfc.
  Hint Unfold response_crc_cls.

  (** Specifications. **)
  Theorem create_response_from_buffer_spec :
    forall size mode buf d rd buf' r d',
      create_response_from_buffer size mode buf = (rd, buf') ->
      rd d = (r, d') ->
      response_queue d = response_queue d' /\
      buf = buf' /\
      (forall res, r = Some res ->
       exists b, response_content res = Some b /\
       length b <= size /\
       substring 0 size buf = b).
  Proof.
    autounfold. intros.
    repeat split; inversion H; subst;
      simpl in *; inversion H0; auto.
    intros. exists (substring 0 size buf').
    inversion H1; simpl; repeat split; auto.
    apply substring_length.
  Qed.

  Lemma create_response_from_callback_spec :
    forall size blk_size crc resource crfc d r d',
      create_response_from_callback size blk_size crc resource crfc d = (r, d') ->
      response_queue d = response_queue d' /\
      (forall res, r = Some res ->
       response_crc res = Some crc /\
       response_crfc res = Some crfc /\
       response_crc_cls res = Some resource).
  Proof.
    autounfold. intros. split; inversion H; auto.
    intros. inversion H0; simpl; repeat split; auto.
  Qed.

  Lemma queue_response_spec :
    forall conn status res b d d',
      queue_response conn status res d = (b, d') ->
      (forall r, In r (response_queue d) -> In r (response_queue d')) /\
      In (conn, status, res) (response_queue d').
  Proof.
    autounfold. intros. inversion H. split; simpl; auto.
  Qed.
    
End SimpleHttpd.
