Require Import List.
Require Import String.

Require Import Buffer.
Require Import Resource.

Inductive responseMemoryMode : Type :=
| Persistent : responseMemoryMode
| MustFree : responseMemoryMode
| MustCopy : responseMemoryMode.

Module Type Httpd (res: Resource).
  Parameter daemon : Type.
  Parameter response : Type.
  Parameter connection : Type.
  Definition DM ( A : Type ) := daemon -> (A * daemon).

  Definition RS ( A : Type ) := res.resource -> (A * res.resource).
  
  (** Callbacks. Used as function pointers in C program. **)
  Definition contentReaderCallback : Type :=
    res.class -> nat -> nat -> buffer (RS bool).

  Definition contentReaderFreeCallback : Type :=
    res.class -> RS unit.

  (** Httpd interfaces. **)
  Parameter create_response_from_buffer :
    nat -> responseMemoryMode -> buffer (DM (option response)).
  Parameter create_response_from_callback :
    nat -> nat -> contentReaderCallback -> res.resource ->
    contentReaderFreeCallback -> DM (option response).
  Parameter queue_response :
    connection -> nat -> response -> DM bool.

  (** Abstract states. **)
  Parameter response_queue : daemon -> list (connection * nat * response).
  Parameter response_content : response -> option string.
  Parameter response_crc : response -> option contentReaderCallback.
  Parameter response_crfc : response -> option contentReaderFreeCallback.
  Parameter response_crc_cls : response -> option res.resource.

  (** Specifications. **)
  Axiom create_response_from_buffer_spec :
    forall size mode buf d rd buf' r d',
      create_response_from_buffer size mode buf = (rd, buf') ->
      rd d = (r, d') ->
      response_queue d = response_queue d' /\
      buf = buf' /\
      (forall res, r = Some res ->
       exists b, response_content res = Some b /\
       length b <= size /\
       substring 0 size buf = b).

  Axiom create_response_from_callback_spec :
    forall size blk_size crc resource crfc d r d',
      create_response_from_callback size blk_size crc resource crfc d = (r, d') ->
      response_queue d = response_queue d' /\
      (forall res, r = Some res ->
       response_crc res = Some crc /\
       response_crfc res = Some crfc /\
       response_crc_cls res = Some resource).

  Axiom queue_response_spec :
    forall conn status res b d d',
      queue_response conn status res d = (b, d') ->
      (forall r, In r (response_queue d) -> In r (response_queue d')) /\
      In (conn, status, res) (response_queue d').
End Httpd.
