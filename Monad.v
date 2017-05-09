Class Monad ( M : Type -> Type ) : Type :=
  { ret { A : Type } : A -> M A;
    bind { A B : Type } : (A -> M B) -> M A -> M B }.

Notation "x <- P ; Q" := (bind (fun x => Q) P) (at level 100).

Notation "P >> Q" := (bind (fun _ => Q) P) (at level 100).

Instance Option_Monad : Monad option :=
  { ret A x := Some x;
    bind A B f a := match a with
                    | Some a' => f a'
                    | None => None
                    end }.
