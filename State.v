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
