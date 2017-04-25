Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Require Import Utility.
Require Import InvTactics.
Require Import FileSystem.

Module SimpleFS : FileSystem.

  Definition path : Type := string.
  Definition file_content : Type := bool.
  Definition file : Type := unit.
  Definition file_handle : Type := nat.
  Definition metadata : Type := nat.

  Record file_stat : Type :=
    mkStat { is_reg : bool;
           is_dir : bool;
           is_chr : bool;
           is_blk : bool;
           is_fifo : bool;
           is_lnk : bool;
           is_sock : bool
           }.

  Definition file_name : string := "file".

  Definition fsContents (p : path) : option (list bool) :=
    if strcmp p file_name then
      Some (true :: nil)
    else None.
    
  Record file_system : Type :=
    mkFS { is_open : bool;
           is_read : bool;
           has_fd : bool;
           the_stat : file_stat
         }.

  Definition init_file_stat : file_stat :=
    mkStat true false false false false false false.
  Definition initial_fs : file_system :=
    mkFS false false false init_file_stat.

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

  Definition abs_fstat (f : file_stat) : abstract_file_stat :=
    abs_stat (is_reg f) (is_dir f) (is_chr f) (is_blk f)
             (is_fifo f) (is_lnk f) (is_sock f).

  Definition init_abs_fstat := abs_fstat init_file_stat.

  Definition abs_fs (fs: file_system) : abstract_file_system :=
    abs fsContents (if is_open fs then tt::nil else nil)
        (fun _ => if is_open fs then
                 Some (abs_file file_name (if is_read fs then 1 else 0)
                                init_abs_fstat)
               else None)
        (fun _ => if (has_fd fs) then Some 1 else None).

  Theorem abstract_file_system_spec : forall fs f,
      forall afs, afs = abs_fs fs ->
             (In f (streams afs) <-> file_info afs f <> None) /\
             (forall fi, file_info afs f = Some fi ->
                    contents afs (p fi) <> None).
  Proof.
    intros. split; unfold abs_fs in H; subst; simpl.
    - split; intros; destruct (is_open fs) eqn:Hopen;
        destruct f; try intro; try solve by inversion;
          simpl; auto.
    - intros.
      destruct (is_open fs); subst; inversion H;
        simpl; intro; try solve by inversion.
  Qed.
  
  Definition fopen (p: path) (m : file_access_mode) : FS (option file) :=
    fun fs => match m with
           | wb => (None, fs)
           | ab => (None, fs)
           | rb => if strcmp p file_name then
                    (Some tt, mkFS true (is_read fs) (has_fd fs) (the_stat fs))
                  else (None, fs)
           end.

  Theorem fopen_spec : forall p m f fs fs',
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
  Proof.
    intros. repeat split.
    - intros; subst.
      inversion H3. unfold fsContents in H1.
      unfold fopen in H.
      destruct (strcmp p0 file_name).
      + try solve by inversion.
      + inversion H; auto.
    - intros. destruct H2; subst; simpl in *; try solve by inversion.
    - intros. subst. destruct m; simpl in H; try solve by inversion.
      destruct (strcmp p0 file_name); try solve by inversion.
      inversion H. simpl. auto.
    - intros. subst.
      destruct m; simpl in H; 
        destruct (strcmp p0 file_name); inversion H; simpl; auto.
    - subst.
      destruct m; simpl in H; destruct (strcmp p0 file_name);
        inversion H; subst; auto.
      + simpl. destruct (is_open fs); auto.
        destruct f'. contradiction.
    - destruct f.
      + destruct f; destruct f'. contradiction.
      + destruct m; simpl in H; destruct (strcmp p0 file_name);
          subst; inversion H; auto.
    - intros; subst. simpl; auto.
  Qed.

  Definition fileno (f : file) : FS (option file_handle) :=
    fun fs => if (is_open fs) then
             (Some 1, mkFS (is_open fs) (is_read fs) true (the_stat fs))
           else (None, fs).

  Theorem fileno_spec : forall f fs fs' fd,
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
  Proof.
    intros. unfold fileno in H.
    destruct (is_open fs) eqn:Hopen.
    - repeat split; subst; inversion H; simpl; auto;
        try (destruct f; destruct f'; contradiction);
          try (rewrite Hopen); auto;
            try solve [destruct f; simpl; intro Hc; exfalso; apply Hc; auto].
      + destruct (has_fd fs); auto. intro. contradiction.
    - repeat split; subst; inversion H; simpl; auto;
        try (destruct f; destruct f'; contradiction);
        destruct (has_fd fs) eqn:Hfd; inversion H; subst;
          try (rewrite Hopen); try (rewrite Hfd); auto;
            try solve [unfold abs_fs in H2; rewrite Hopen in H2;
                       simpl in H2; exfalso; auto].
  Qed.

  Definition fseek (f : file) (off : nat) (s : seek_set) : FS bool :=
    fun fs => if negb (is_open fs) then
             (false, fs)
           else if (1 <=? off) then
                  (true, mkFS true true (has_fd fs) (the_stat fs))
                else match s with
                     | SeekEnd => (true, mkFS true true (has_fd fs) (the_stat fs))
                     | SeekSet => (true, mkFS true false (has_fd fs) (the_stat fs))
                     | _ => (true, fs)
                     end.
  
  Theorem fseek_spec : forall f off origin fs fs' b,
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
  Proof.
    intros.
    destruct off; unfold fseek in H;
      destruct (is_open fs) eqn:Hopen; simpl in H; inversion H; subst;
        destruct origin eqn:Horigin;
        repeat split; try intros; inversion H; subst; auto;
          try (destruct f; destruct f'; contradiction);
          try solve [simpl; rewrite Hopen; destruct f; simpl; auto];
          try solve [simpl in *; rewrite Hopen in *;
                     inversion H0; inversion H1; simpl;
                     try (destruct (is_read fs'));
                     try (simpl; simpl in H2;
                          unfold fsContents in H2; subst;
                          simpl in H2; inversion H2; simpl);
                     try rewrite Nat.min_0_r; reflexivity];
          try (simpl; destruct f'); auto.
    - simpl. simpl in H1; inversion H1. simpl.
      simpl in H2. unfold fsContents in H2.
      simpl in H0. rewrite Hopen in H0. inversion H0.
      subst. simpl in H2. inversion H2. simpl.
      rewrite <- plus_n_Sm. auto.
  Qed.
  
End SimpleFS.
