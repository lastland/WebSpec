Require Import List.
Require Import String.

Require Import Resource.
Require Import FileSystem.

Module FSResource <: Resource.
  Declare Module FS : FileSystem.
  Definition resource : Type := (FS.file_system * FS.file).
End FSResource.  
