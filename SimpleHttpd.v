Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.

Require Import Monad.
Require Import InvTactics.
Require Import Buffer.
Require Import StringUtility.
Require Import Resource.
Require Import HttpdInterface.

Module SimpleHttpd (res: Resource) : Httpd (res).
  Definition RS ( A : Type ) := res.resource -> (A * res.resource).

  (** Callbacks. **)
  Definition contentReaderCallback : Type :=
    res.class -> nat -> nat -> string -> RS (nat * string).

  Definition contentReaderFreeCallback : Type :=
    res.class -> RS unit.

  (** Data types. **)
  Record _response := mkRes {
                          content : option string;
                          crc : option contentReaderCallback;
                          crfc : option contentReaderFreeCallback;
                          crc_cls : option res.class
                        }.
  
  Definition connection : Type := nat.
  Definition response : Type := _response.
  Definition daemon : Type := list (connection * nat * response).
  Definition DM ( A : Type ) := daemon -> (A * daemon).
  Instance DM_Monad : Monad DM :=
    { ret A x := fun d => (x, d);
      bind A B f x := fun d => match x d with
                            | (y, d') => f y d'
                            end }.

  (** Httpd interfaces. **)
  Definition create_response_from_buffer (size: nat) (mode: responseMemoryMode) :
    string -> DM (option response * string) :=
    fun buf d => ((Some (mkRes (Some (substring 0 size buf)) None None None),
                buf), d).

  Definition create_response_from_callback (size: nat) (blk_size: nat)
             (crc: contentReaderCallback) (r: res.class)
             (crfc: contentReaderFreeCallback) : DM (option response) :=
    fun d => (Some (mkRes None (Some crc) (Some crfc) (Some r)), d).

  Definition queue_response (conn: option connection)
             (code: nat) (res: option response) : DM bool :=
    fun d => match conn with
          | None => (false, d)
          | Some c =>
            match res with
            | None => (false, d)
            | Some r =>
              (true, (c, code, r) :: d)
            end
          end.

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
    option res.class := crc_cls r.

  Hint Unfold response_queue.
  Hint Unfold response_content.
  Hint Unfold response_crc.
  Hint Unfold response_crfc.
  Hint Unfold response_crc_cls.

  (** Specifications. **)
  Theorem create_response_from_buffer_spec :
    forall size mode buf d buf' r d',
      create_response_from_buffer size mode buf d = ((r, buf'), d') ->
      response_queue d = response_queue d' /\
      buf = buf' /\
      (forall res, r = Some res ->
       exists b, response_content res = Some b /\
       length b <= size /\
       substring 0 size buf = b).
  Proof.
    autounfold. intros.
    repeat split; inversion H; subst; auto.
    intros. exists (substring 0 size buf').
    inversion H0; simpl; repeat split; auto.
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
      (forall c r, conn = Some c -> res = Some r ->
              In (c, status, r) (response_queue d')).
  Proof.
    autounfold. intros. inversion H.
    split; intros; destruct conn; destruct res; inversion H; simpl; subst.
    all: repeat match goal with
               [ H : Some ?a = Some ?b |- _ ] =>
               inversion H; clear H end.
    all: auto.
    all: try solve by inversion.
  Qed.
    
End SimpleHttpd.
