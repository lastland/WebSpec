Require Import List.
Require Import String.

Require Import Resource.

Module Type Httpd.

  Declare Module Res : Resource.
  
  Inductive responseMemoryMode : Type :=
  | Persistent : responseMemoryMode
  | MustFree : responseMemoryMode
  | MustCopy : responseMemoryMode.

  Definition contentReaderCallback : Type :=
    Res.resource -> nat -> string -> nat -> nat.

  Definition contentReaderFreeCallback : Type :=
    Res.resource -> Res.resource.
  
  Parameter response : Type.
  Parameter connection : Type.
  Parameter createResponseFromBuffer :
    nat -> string -> responseMemoryMode -> response.
  Parameter createResponseFromCallback :
    nat -> nat -> contentReaderCallback -> Res.resource ->
    contentReaderFreeCallback -> response.
  Parameter queueResponse :
    connection -> nat -> response -> option connection.

  Parameter response_in_queue : connection -> response -> bool.
  Definition response_in_queue_option
             (conn : option connection) (res : response) : bool :=
    match conn with
    | Some c => response_in_queue c res
    | None => true
    end.
  Axiom response_in_queue_after_queue_response :
    forall conn n res, response_in_queue_option (queueResponse conn n res) res = true.
End Httpd.
