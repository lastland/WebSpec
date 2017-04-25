Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

(** Only binary access modes -- this is only temporary. **)
Inductive file_access_mode : Type :=
| rb : file_access_mode
| wb : file_access_mode
| ab : file_access_mode.

Inductive seek_set : Type :=
| SeekSet : seek_set
| SeekCur : seek_set
| SeekEnd : seek_set.

Definition expected_offset (origin : seek_set) (l e o : nat) : nat :=
  match origin with
  | SeekSet => o
  | SeekCur => l + o
  | SeekEnd => e + o
  end.

Module Type FileSystem.
  Parameter file_system : Type.
  Parameter initial_fs : file_system.
  Parameter path : Type.
  Parameter file : Type.
  Parameter file_handle : Type.
  Parameter file_stat : Type.

  Record abstract_file_stat : Type :=
    abs_stat { isReg : bool;
               isDir : bool;
               isChr : bool;
               isBlk : bool;
               isFifo : bool;
               isLnk : bool;
               isSock : bool
             }.
  
  Record abstract_file_metainfo : Type :=
    abs_file { p : path;
               offset : nat;
               stat : abstract_file_stat
             }.

  Record abstract_file_system : Type :=
    abs { contents : path -> option (list bool);
          streams : list file;
          file_info : file -> option abstract_file_metainfo;
          file_no : file -> option file_handle
        }.

  Definition FS ( A : Type ) := file_system -> (A * file_system).

  Parameter abs_fs : file_system -> abstract_file_system.
  Parameter abs_fstat : file_stat -> abstract_file_stat.
  
  Axiom abstract_file_system_spec : forall fs f,
      forall afs, afs = abs_fs fs ->
             (In f (streams afs) <-> file_info afs f <> None) /\
             (forall fi, file_info afs f = Some fi ->
                    contents afs (p fi) <> None).
  
  (** Functions related to file system.
      Here we only specify what we need in our web server. 
   **)
  Parameter fopen : path -> file_access_mode -> FS (option file).
  Parameter fileno : file -> FS (option file_handle).
  Parameter fseek : file -> nat -> seek_set -> FS bool.
  Parameter fread : file -> nat -> nat -> FS (list (list bool) * nat).
  Parameter fclose : file -> FS bool.
  Parameter fstat : file_handle -> file_system -> option file_stat.

  Parameter is_reg : file_stat -> bool.
  Parameter is_dir : file_stat -> bool.

  (** Specifications for file operations with regards to abstract
      file system. Our web server does not write to file systems,
      so there's no need to consider consistency.
   **)
  
  Axiom fopen_spec : forall p m f fs fs',
      fopen p m fs = (f, fs') ->
      forall afs, afs = abs_fs fs ->
      forall afs', afs' = abs_fs fs' ->
      (m = rb -> contents afs p = None -> f = None) /\
      (m = wb \/ m = ab ->
       forall f', f = Some f' ->
             contents afs' p <> None) /\
      (forall f', f = Some f' ->
             In f' (streams afs')) /\
      (forall f', file_no afs f' = file_no afs' f') /\
      (forall f', f <> Some f' ->
             file_info afs f' = file_info afs' f' /\
             In f' (streams afs) = In f' (streams afs')) /\
      (forall p', p <> p' \/ m = rb ->
             contents afs p' = contents afs' p').

  Axiom fileno_spec : forall f fs fs' fd,
      fileno f fs = (fd, fs') ->
      forall afs, afs = abs_fs fs ->
      forall afs', afs' = abs_fs fs' ->       
      (In f (streams afs) ->
       file_no afs' f = fd /\
       (file_no afs f <> None -> file_no afs f = fd)) /\
      (~ In f (streams afs) -> fd = None) /\
      (forall f', f' <> f ->
             file_no afs' f <> file_no afs' f' /\
             file_no afs f' = file_no afs' f') /\
      (forall f', file_info afs f' = file_info afs' f') /\
      (forall f', In f' (streams afs) <-> In f' (streams afs')) /\
      (forall p', contents afs p' = contents afs' p').

  Axiom fseek_spec : forall f off origin fs fs' b,
      fseek f off origin fs = (b, fs') ->
      forall afs, afs = abs_fs fs ->
      forall afs', afs' = abs_fs fs' ->       
      (In f (streams afs) <-> b = true) /\
      (forall f', file_no afs f' = file_no afs' f') /\
      (forall f', f <> f' -> file_info afs f' = file_info afs' f') /\
      (forall fi,  file_info afs  f = Some fi  ->
       forall fi', file_info afs' f = Some fi' ->
       forall s, contents afs (p fi) = Some s ->
            offset fi' = min (length s) (expected_offset origin (offset fi) (length s) off)) /\
      (forall f', In f' (streams afs) <-> In f' (streams afs')) /\
      (forall p', contents afs p' = contents afs' p').

  Axiom fread_spec : forall f size count fs fs' buf r,
      fread f size count fs = ((buf, r), fs') ->
      forall afs, afs = abs_fs fs ->
      forall afs', afs' = abs_fs fs' ->
      (r <= count) /\
      (length (filter (fun b => beq_nat (length b) size) buf) = r) /\
      (~ In f (streams afs) -> buf = nil /\ r = 0) /\
      (forall f', file_no afs f' = file_no afs' f') /\
      (forall f', f <> f' ->
             file_info afs f' = file_info afs' f') /\
      (forall l, l = fold_left (fun x y => x + length y) buf 0 ->
       forall fi,  file_info afs  f = Some fi  ->
       forall fi', file_info afs' f = Some fi' ->
       forall s, contents afs (p fi) = Some s ->
            l <= (length s - offset fi) /\ offset fi' = offset fi + l) /\
      (forall f', In f' (streams afs) <-> In f' (streams afs')) /\
      (forall p', contents afs p' = contents afs' p').

  Axiom fclose_spec : forall f fs fs' b,
      fclose f fs = (b, fs') ->
      forall afs, afs = abs_fs fs ->
      forall afs', afs' = abs_fs fs' ->
      (~ In f (streams afs) -> b = false) /\
      ~ In f (streams afs') /\
      (forall f', file_no afs f' = file_no afs' f') /\
      (forall f', f <> f' ->
             file_info afs f' = file_info afs' f' /\
             In f' (streams afs) = In f' (streams afs')) /\
      (forall p', contents afs p' = contents afs' p').

  Axiom fstat_spec : forall f fd fs st,
      forall afs, abs_fs fs = afs ->
      file_no afs f = Some fd ->
      fstat fd fs = st ->
      forall fi, file_info afs f = Some fi ->
      forall st', st = Some st' ->
      stat fi = abs_fstat st'.

  Axiom is_reg_spec : forall st,
      is_reg st = isReg (abs_fstat st).

  Axiom is_dir_spec : forall st,
      is_dir st = isDir (abs_fstat st).
  
End FileSystem.
