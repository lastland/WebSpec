Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.omega.Omega.

Require Import Utility.
Require Import InvTactics.
Require Import FileSystem.

Module SimpleFS : FileSystem.

  Definition path : Type := string.
  Definition file_content : Type := bool.
  Definition file : Type := unit.
  Definition file_handle : Type := nat.
  Definition metadata : Type := nat.

  Record file_stat' : Type :=
    mkStat { is_reg : bool;
           is_dir : bool;
           is_chr : bool;
           is_blk : bool;
           is_fifo : bool;
           is_lnk : bool;
           is_sock : bool
           }.

  Definition file_stat : Type := file_stat'.

  Definition file_name : string := "file".

  Definition fsContents (p : path) : option (list bool) :=
    if strcmp p file_name then
      Some (true :: nil)
    else None.

  Hint Unfold fsContents.
    
  Record file_system' : Type :=
    mkFS { is_open : bool;
           is_read : bool;
           has_fd : bool;
           the_stat : file_stat
         }.

  Definition file_system : Type := file_system'.

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

  Definition abs_fstat (f : file_stat) : abstract_file_stat :=
    abs_stat (is_reg f) (is_dir f) (is_chr f) (is_blk f)
             (is_fifo f) (is_lnk f) (is_sock f).

  Definition init_abs_fstat := abs_fstat init_file_stat.
  
  Definition contents (fs : file_system) := fsContents.
  Definition streams (fs : file_system) :=
    if is_open fs then tt::nil else nil.
  Definition file_info (fs : file_system) (_ : file) :=
    if is_open fs then
      Some (abs_file file_name (if is_read fs then 1 else 0)
                     init_abs_fstat)
    else None.
  Definition file_no (fs : file_system) (_ : file) :=
    if (has_fd fs) then Some 1 else None.
  
  Definition FS ( A : Type ) := file_system -> (A * file_system).

  Hint Unfold contents.
  Hint Unfold streams.
  Hint Unfold file_info.
  Hint Unfold file_no.

  (*
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
   *)
  
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
      (m = rb -> contents fs p = None -> f = None) /\
      (m = wb \/ m = ab ->
       forall f', f = Some f' ->
             contents fs' p <> None) /\
      (forall f', f = Some f' ->
             In f' (streams fs')) /\
      (forall f', file_no fs f' = file_no fs' f') /\
      (forall f', f <> Some f' ->
             file_info fs f' = file_info fs' f' /\
             In f' (streams fs) = In f' (streams fs')) /\
      (forall p', p <> p' \/ m = rb ->
             contents fs p' = contents fs' p').
  Proof.
    intros. repeat split.
    - intros; subst.
      unfold contents in H1. unfold fsContents in H1.
      unfold fopen in H.
      destruct (strcmp p0 file_name).
      + try solve by inversion.
      + inversion H; auto.
    - intros. destruct H0; subst; simpl in *; try solve by inversion.
    - intros. subst. destruct m; simpl in H; try solve by inversion.
      destruct (strcmp p0 file_name); try solve by inversion.
      inversion H. simpl. auto.
    - intros. subst.
      destruct m; simpl in H; 
        destruct (strcmp p0 file_name); inversion H; simpl; auto.
    - subst.
      destruct m; simpl in H; destruct (strcmp p0 file_name);
        inversion H; subst; auto.
      + simpl. destruct (is_open fs); destruct f'; contradiction.
    - destruct f.
      + destruct f; destruct f'. contradiction.
      + destruct m; simpl in H; destruct (strcmp p0 file_name);
          subst; inversion H; auto.
  Qed.

  Definition fileno (f : file) : FS (option file_handle) :=
    fun fs => if (is_open fs) then
             (Some 1, mkFS (is_open fs) (is_read fs) true (the_stat fs))
           else (None, fs).

  Theorem fileno_spec : forall f fs fs' fd,
      fileno f fs = (fd, fs') ->
      (In f (streams fs) ->
       file_no fs' f = fd /\
       (file_no fs f <> None -> file_no fs f = fd)) /\
      (~ In f (streams fs) -> fd = None) /\
      (forall f', f' <> f ->
             file_no fs' f <> file_no fs' f' /\
             file_no fs f' = file_no fs' f') /\
      (forall f', file_info fs f' = file_info fs' f') /\
      (forall f', In f' (streams fs) <-> In f' (streams fs')) /\
      (forall p', contents fs p' = contents fs' p').
  Proof.
    intros. unfold fileno in H.
    destruct (is_open fs) eqn:Hopen.
    - repeat split; subst; inversion H; subst; simpl; auto.
      all: try (destruct f; destruct f'; contradiction).
      all: autounfold; try rewrite Hopen; simpl; auto.
      + destruct (has_fd fs); auto; contradiction.
      + destruct f. intros. destruct H0. simpl. auto.
    - repeat split; subst; inversion H; subst; simpl; auto.
      all: try (destruct f; destruct f'; contradiction).
      all: autounfold in *; rewrite Hopen in *;
        destruct f; simpl in *; try solve by inversion.
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
      (In f (streams fs) <-> b = true) /\
      (forall f', file_no fs f' = file_no fs' f') /\
      (forall f', f <> f' -> file_info fs f' = file_info fs' f') /\
      (forall fi,  file_info fs  f = Some fi  ->
       forall fi', file_info fs' f = Some fi' ->
       forall s, contents fs (p fi) = Some s ->
            offset fi' = min (length s) (expected_offset origin (offset fi) (length s) off)) /\
      (forall f', In f' (streams fs) <-> In f' (streams fs')) /\
      (forall p', contents fs p' = contents fs' p').
  Proof.
    intros.
    destruct off; unfold fseek in H;
      destruct (is_open fs) eqn:Hopen; simpl in H; inversion H; subst;
        destruct origin eqn:Horigin; repeat split.
    all: try intros; inversion H; subst; auto.
    all: autounfold in *; rewrite Hopen in *.
    all: try (destruct f).
    all: try (destruct f').
    all: simpl in *; auto; try contradiction.
    all: try
           (match goal with
              [ H : fsContents ?pi = Some ?s |- _ ] => 
              autounfold in H; destruct (strcmp pi file_name); inversion H end).
    all: try inversion H0; simpl; auto.
    all: try inversion H1; simpl; auto.
    all: try inversion H2; simpl; auto.
    - destruct (is_read fs'); simpl; auto.
    - destruct (is_read fs); simpl; auto.
  Qed.

  Definition fread (f : file) (size : nat) (count : nat) : FS (list (list bool) * nat) :=
    fun fs => if (beq_nat size 0) then
             ((nil, 0), fs)
           else if (beq_nat count 0) then
                  ((nil, 0), fs)
                else if (is_open fs) then
                       if (is_read fs) then
                         ((nil, 0), fs)
                       else
                         (((true::nil)::nil, if (beq_nat size 1) then 1 else 0),
                          mkFS true true (has_fd fs) (the_stat fs))
                     else ((nil, 0), fs).

  Theorem fread_spec : forall f size count fs fs' buf r,
      fread f size count fs = ((buf, r), fs') ->
      (r <= count) /\
      (length (filter (fun b => beq_nat (length b) size) buf) = r) /\
      (~ In f (streams fs) -> buf = nil /\ r = 0) /\
      (forall f', file_no fs f' = file_no fs' f') /\
      (forall f', f <> f' ->
             file_info fs f' = file_info fs' f') /\
      (forall l, l = fold_left (fun x y => x + length y) buf 0 ->
       forall fi,  file_info fs  f = Some fi  ->
       forall fi', file_info fs' f = Some fi' ->
       forall s, contents fs (p fi) = Some s ->
            l <= (length s - offset fi) /\ offset fi' = offset fi + l) /\
      (forall f', In f' (streams fs) <-> In f' (streams fs')) /\
      (forall p', contents fs p' = contents fs' p').
  Proof.
    intros. repeat split.
    all: try match goal with
               [ H : fread _ _ _ _ = _ |- _ ] =>
               unfold fread in H;
                 destruct (beq_nat size 0) eqn:Hsize;
                 destruct (beq_nat count 0) eqn:Hcount;
                 destruct (is_open fs) eqn:Hopen;
                 destruct (is_read fs) eqn:Hread; 
                 try solve [inversion H; omega];
                 try solve [inversion H; simpl; auto];
                 try solve [destruct (beq_nat size 1) eqn:Hsize';
                            inversion H; try apply beq_nat_false in Hcount; omega]
             end.
    all: autounfold in *.
    all: try (rewrite Hopen in *).
    all: try (destruct f'; intros).
    all: try solve [destruct f; destruct H0; simpl; auto].
    all: try
           (match goal with
              [ H : fsContents ?pi = Some ?s |- _ ] => 
              autounfold in H; destruct (strcmp pi file_name); inversion H end).
    all: try (inversion H1; simpl; rewrite Hread;
              inversion H; subst; simpl; auto).
    all: try simpl in H2.
    all: try (rewrite Hopen in H2; rewrite Hread in H2).
    all: try (inversion H2; simpl; auto).
    all: try (inversion H).
    all: simpl; auto.
    - destruct size eqn:Hsize'; try solve by inversion.
      simpl in H. destruct n; simpl in H; inversion H; simpl; auto.
  Qed.

  Definition fclose (f : file) : FS bool :=
    fun fs => if (is_open fs) then
             (true, mkFS false false (has_fd fs) (the_stat fs))
           else (false, fs).

  Theorem fclose_spec : forall f fs fs' b,
      fclose f fs = (b, fs') ->
      (~ In f (streams fs) -> b = false) /\
      ~ In f (streams fs') /\
      (forall f', file_no fs f' = file_no fs' f') /\
      (forall f', f <> f' ->
             file_info fs f' = file_info fs' f' /\
             In f' (streams fs) = In f' (streams fs')) /\
      (forall p', contents fs p' = contents fs' p').
  Proof.
    intros. unfold fclose in H.
    destruct (is_open fs) eqn:Hopen; inversion H; repeat split.
    all: autounfold.
    all: destruct f. 
    all: try rewrite Hopen; simpl; auto.
    all: try (destruct f'; contradiction).
    - intros. destruct H0. auto.
    - subst. rewrite Hopen. auto.
  Qed.

  Definition fstat (fd : file_handle) (fs : file_system) : option file_stat :=
    if (beq_nat fd 1) then
      Some init_file_stat
    else None.

  Theorem fstat_spec : forall f fd fs st,
      file_no fs f = Some fd ->
      fstat fd fs = st ->
      forall fi, file_info fs f = Some fi ->
      forall st', st = Some st' ->
      stat fi = abs_fstat st'.
  Proof.
    intros. autounfold in *.
    destruct (beq_nat fd 1) eqn:Heq; subst.
    all: unfold fstat in H2; rewrite Heq in H2; inversion H2.
    subst. unfold abs_fstat. simpl in *.
    destruct (is_open fs); destruct (has_fd fs);
      try solve by inversion.
    inversion H1. simpl. auto.
  Qed.

  Theorem is_reg_spec : forall st,
      is_reg st = isReg (abs_fstat st).
  Proof.
    intros. reflexivity.
  Qed.

  Theorem is_dir_spec : forall st,
      is_dir st = isDir (abs_fstat st).
  Proof.
    intros. reflexivity.
  Qed.

End SimpleFS.
