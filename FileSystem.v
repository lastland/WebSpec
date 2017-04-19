Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Module Type FileSystem.
  (** This is the abstraction of the whole file system.
      It does not correspond to any explicit data structures in C code.
      It is, instead, used to reason about side effects happened in the C code. 
   **)
  Parameter file_system : Type.
  
  (** The following parameters correspond to C code. **)
  Parameter file : Type.
  Parameter file_handler : Type.
  Parameter file_stat : Type.

  (* this definition may not be accurate, but let's use it for now. *)
  Inductive file_access_mode : Type :=
  | r : file_access_mode
  | w : file_access_mode
  | a : file_access_mode
  | rb : file_access_mode
  | wb : file_access_mode
  | ab : file_access_mode.

  Inductive seek_set : Type :=
  | SeekSet : seek_set
  | SeekCur : seek_set
  | SeekEnd : seek_set.
  
  Parameter fopen : file_system -> string -> file_access_mode -> option file.
  Parameter fileno : file -> option file_handler.
  Parameter fstat : file_handler -> option file_stat.
  Parameter fclose : file -> file_system.

  Parameter fseek : file_system -> file -> nat -> seek_set -> nat -> file_system.
  Parameter fread : file_system -> file -> nat -> nat -> (string * nat).

  Parameter is_reg : file_stat -> bool.
  Parameter is_dir : file_stat -> bool.

  (** Some properties about file system.
      Again, this part does not correspond to the C code.
      Instead, they are used for specifying the C code.
   **)
  Parameter is_open : file_system -> file -> bool.

  Definition is_open_option (fs : file_system) (file : option file) : bool :=
      match file with
      | Some f => is_open fs f
      | _ => true
      end.
  
  Parameter is_closed : file_system -> file -> bool.

  Axiom fopen_will_open_file : forall fs file_name mode,
      is_open_option fs (fopen fs file_name mode) = true.

  Axiom fclose_will_close_file : forall file,
      is_closed (fclose file) file = true.

End FileSystem.
