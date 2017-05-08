Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ListUtility.
Require Import InvTactics.
Require Import HttpRequest.
Require Import HttpResponse.
Require Import State.

Definition genResponse (req: HttpRequest) : HttpResponse :=
  if (is_complete_request req) then
    Res_HeaderPart "" :: Res_BodyPart "" :: nil
  else nil.

Definition Connection : Type := (State * HttpRequest * HttpResponse).

Definition transition (f : HttpRequest -> HttpResponse)
           (c : Connection) (req : option HttpRequestLine) :
  Connection * option HttpResponsePart :=
  let '(s, reqs, res) := c in
  match s with
  | Init =>
    match req with
    | Some (Req_InitialMessage _ as r) =>
      ((UrlReceived, (r :: reqs), res), None)
    | Some r => ((Closed, r :: reqs, res), None)
    | None => ((Closed, reqs, res), None)
    end
  | UrlReceived =>
    match req with
    | None => ((HeadersReceived, reqs, res), None)
    | Some r => match r with
               | Req_InitialMessage _ as line =>
                 ((Closed, line :: reqs, res), None)
               | Req_HeaderLine _ as line =>
                 ((HeaderPartReceived, line :: reqs, res), None)
               | line => ((Closed, line :: reqs, res), None)
               end
    end
  | HeaderPartReceived =>
    match req with
    | None => ((HeadersReceived, reqs, res), None)
    | Some r => match r with
               | Req_InitialMessage _ as line =>
                 ((Closed, line :: reqs, res), None)
               | line =>
                 ((HeaderPartReceived, line :: reqs, res), None)
               end
    end
  | HeadersReceived =>
    ((HeadersProcessed, reqs, res), None)
  | HeadersProcessed =>
    ((FootersReceived, reqs, res), None)
  | FootersReceived =>
    ((HeadersSending, reqs, f (rev reqs)), None)
  | HeadersSending =>
    match res with
    | Res_HeaderPart _ as part :: res' =>
      ((HeadersSending, reqs, res'), Some part)
    | Res_BodyPart _ as part :: res' =>
      ((HeadersSent, reqs, res'), Some part)
    | nil => ((HeadersSent, reqs, nil), None)
    end
  | HeadersSent =>
    ((NormalBodyUnready, reqs, res), None)
  | NormalBodyUnready =>
    ((NormalBodyReady, reqs, res), None)
  | NormalBodyReady =>
    match res with
    | Res_BodyPart _ as part :: res' =>
      ((NormalBodyReady, reqs, res'), Some part)
    | Res_HeaderPart _ as part :: res' =>
      ((Closed, reqs, res'), Some part)
    | nil =>
      ((FootersSent, reqs, nil), None)
    end
  | FootersSent =>
    ((Closed, reqs, res), None)
  | _ => ((Closed, reqs, res), None)
  end.
