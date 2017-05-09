Require Import Monad.

Module Type Resource.
  Parameter resource : Type.
  Parameter class : Type.
  
  Definition RS ( A : Type ) := resource -> (A * resource).
End Resource.
