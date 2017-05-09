Require Import List.
Require Import String.

Require Import Monad.
Require Import Resource.
Require Import FileSystem.

Module FSResource (FS : FileSystem) <: Resource.
  Definition resource : Type := FS.file_system.
  Definition class : Type := FS.file.

  Definition RS ( A : Type ) := resource -> (A * resource).
End FSResource.  
