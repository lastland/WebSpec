Require Import List.
Require Import String.

Require Import Resource.
Require Import FileSystem.

Module FSResource (FS : FileSystem) <: Resource.
  Definition resource : Type := (FS.file_system * FS.file).
  Definition class : Type := FS.file.
End FSResource.  
