(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Gauss elimination of matrix
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
  1. Two stages
     First stage, we use a simple case of `n × n` matrix
     Second stage, we should consider the case of `m × n` matrix

  2. learn "fold_left" and "fold_right"

     fold_left  f [b1;b2;b3] a = f (f (f a b1) b2) b3
     Folding start from newest added element.

     fold_right f a [b1;b2;b3] = f b1 (f b2 (f b3 a))
     Folding start from oldest added element.
 *)

Require Export Matrix.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv.

(** fold_left f (map g l) a = fold_left (fun x y => f x (g y)) l a *)
Lemma fold_left_map :
  forall {tA tB} (l : list tB) (f : tA -> tA -> tA) (g : tB -> tA) a,
    fold_left f (map g l) a = fold_left (fun x y => f x (g y)) l a.
Proof.
  intros tA tB l. induction l; intros; simpl. auto.
  rewrite IHl. auto.
Qed.

(** fold_right f a (map g l) = fold_right (fun x y => f (g x) y) a l *)
Lemma fold_right_map :
  forall {tA tB} (l : list tB) (f : tA -> tA -> tA) (g : tB -> tA) a,
    fold_right f a (map g l) = fold_right (fun x y => f (g x) y) a l.
Proof.
  intros tA tB l. induction l; intros; simpl. auto.
  rewrite IHl. auto.
Qed.

Section Row_Trans.
    Context `{HField : Field} `{HAeqDec : Dec _ (@eq tA)}.
  Add Field field_inst : (make_field_theory HField).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun a b => a * / b) : A_scope.
  
  Notation mat r c := (mat tA r c).
  Notation smat n := (smat tA n).
  Notation mat1 := (@mat1 _ Azero Aone).
  Notation madd := (@madd _ Aadd).
  Infix "+" := madd : mat_scope.
  Notation mmul := (@mmul _ Aadd Azero Amul).
  Infix "*" := mmul : mat_scope.
  Notation mrowSwap := (@mrowSwap tA).
  Notation mrowScale := (@mrowScale _ Amul).
  Notation mrowAdd := (@mrowAdd _ Aadd Amul).
  Notation mrowSwapM := (@mrowSwapM _ 0 1 _).
  Notation mrowScaleM := (@mrowScaleM _ 0 1 _).
  Notation mrowAddM := (@mrowAddM _ Aadd 0 1 _).
  Notation mrow := (@mrow _ Azero).


  (* ======================================================================= *)
  (** ** 行变换 *)
  
  (* 为避免逆矩阵计算时的大量计算，使用抽象表示，可提高计算效率 *)
  Inductive RowOp {n} :=
  | ROnop
  | ROswap (i j : 'I_(S n))
  | ROscale (i : 'I_(S n)) (c : tA)
  | ROadd (i j : 'I_(S n)) (c : tA).

  (** 行变换列表转换为矩阵 *)
  Definition rowOps2mat {n} (l : list (@RowOp n)) : smat (S n) :=
    fold_right (fun op M =>
    match op with
    | ROnop => M
    | ROswap i j => mrowSwap i j M
    | ROscale i c => mrowScale i c M
    | ROadd i j c => mrowAdd i j c M
     end) mat1 l.

  (** rowOps2mat (l1 ++ l2) = rowOps2mat l1 * rowOps2mat l2 *)
    Theorem rowOps2mat_app : forall {n} (l1 l2 : list (@RowOp n)),
      rowOps2mat (l1 ++ l2) = rowOps2mat l1 * rowOps2mat l2.
    Proof.
    intros. induction l1; intros; simpl.
    - rewrite mmul_1_l; auto.
    - destruct a; auto.
      + rewrite IHl1. rewrite mrowSwap_mmul; auto.
      + rewrite IHl1. rewrite mrowScale_mmul; auto.
      + rewrite IHl1. rewrite mrowAdd_mmul; auto.
  Qed.

  Lemma rowOps2mat_cons : forall {n} (a : @RowOp n) (l : list (@RowOp n)),
    rowOps2mat (a :: l) = rowOps2mat [a] * rowOps2mat l.
  Proof.
    intros. replace (a :: l) with ([a] ++ l)%list by auto.
    apply rowOps2mat_app.
  Qed.


  (* ======================================================================= *)
  (** ** 行变换的逆过程 *)

  (** 行变换列表转换为反作用的矩阵。即，rowOps2mat的逆矩阵 *)
  Definition rowOps2matInv {n} (l : list (@RowOp n)) : smat (S n) :=
    fold_left (fun M op =>
    match op with
    | ROnop => M
    | ROswap i j => mrowSwap i j M
    | ROscale i c => mrowScale i (/c) M
    | ROadd i j c => mrowAdd i j (-c) M
    end) l mat1.

  (* 为证明 rowOps2matInv_app，引入辅助定义和引理，主要思想是：
     将 rowOps2mat 和 rowOps2matInv 转换为矩阵乘法 *)
  
    
    (* Valid RowOp *)
  Definition roValid {n} (op : @RowOp n) : Prop :=
    match op with
    | ROnop => True
    | ROswap i j => True
    | ROscale i c => c <> 0
    | ROadd i j c => i <> j
    end.

    (* op => matrix of op *)
  Definition ro2mat {n} (op : @RowOp n) : smat (S n) :=
    match op with
    | ROnop => mat1
    | ROswap i j => mrowSwapM i j
    | ROscale i c => mrowScaleM i c
    | ROadd i j c => mrowAddM i j c
    end.

    (* op => matrix of inverse opeation *)
  Definition ro2matInv {n} (op : @RowOp n) : smat (S n) :=
    match op with
    | ROnop => mat1
    | ROswap i j => mrowSwapM i j
    | ROscale i c => mrowScaleM i (/c)
    | ROadd i j c => mrowAddM i j (-c)
    end.

  Lemma mmul_ro2mat_l : forall n (op : RowOp) (M : smat (S n)),
    ro2mat op * M =
    match op with
    | ROnop => M
    | ROswap i j => mrowSwap i j M
    | ROscale i c => mrowScale i c M
    | ROadd i j c => mrowAdd i j c M
    end.
  Proof.
    intros. unfold ro2mat. destruct op.
    - apply mmul_1_l.
    - rewrite mrowSwap_eq; auto.
    - rewrite mrowScale_eq; auto.
    - rewrite mrowAdd_eq; auto.
  Qed.

  Lemma mmul_ro2matInv_l : forall n (op : RowOp) (M : smat (S n)),
    ro2matInv op * M =
    match op with
    | ROnop => M
    | ROswap i j => mrowSwap i j M
    | ROscale i c => mrowScale i (/ c) M
    | ROadd i j c => mrowAdd i j (- c) M
      end.
  Proof.
    intros.  unfold ro2matInv. destruct op.
    - apply mmul_1_l.
    - rewrite mrowSwap_eq; auto.
    - rewrite mrowScale_eq; auto.
    - rewrite mrowAdd_eq; auto.
  Qed.
    
  Lemma mmul_ro2mat_ro2matInv : forall {n} (op : @RowOp n),
    roValid op -> ro2mat op * ro2matInv op = mat1.
  Proof.
    intros. hnf in H. destruct op; simpl.
    - rewrite mmul_1_l; auto.
    - rewrite mmul_mrowSwapM_mrowSwapM; auto.
    - rewrite mmul_mrowScaleM_mrowScaleM; auto.
    - rewrite mmul_mrowAddM_mrowAddM; auto.
  Qed.
    
  Lemma mmul_ro2matInv_ro2mat : forall {n} (op : @RowOp n),
    roValid op -> ro2matInv op * ro2mat op = mat1.
  Proof.
    intros. hnf in H. destruct op; simpl.
    - rewrite mmul_1_l; auto.
    - rewrite mmul_mrowSwapM_mrowSwapM; auto.
    - replace c with (/ / c) at 2.
      rewrite mmul_mrowScaleM_mrowScaleM; auto.
      apply field_inv_neq0_iff; auto.
      rewrite field_inv_inv; auto.
    - replace c with (- - c) at 2 by field.
      rewrite mmul_mrowAddM_mrowAddM; auto.
  Qed.

  (** rowOps2mat has an equivalent form with matrix multiplication. *)
  (*     Note that, we won't use this definition to improve performance *)
  Lemma rowOps2mat_eq : forall {n} (l : list (@RowOp n)),
    rowOps2mat l = fold_right mmul mat1 (map ro2mat l).
  Proof.
    intros. unfold rowOps2mat. rewrite fold_right_map. f_equal.
    extensionality M. extensionality op. rewrite mmul_ro2mat_l. auto.
  Qed.

  (** rowOps2matInv has an equivalent form with matrix multiplication. *)
  (*     Note that, we won't use this definition to improve performance *)
  Lemma rowOps2matInv_eq : forall {n} (l : list (@RowOp n)),
    rowOps2matInv l = fold_left (fun x y => y * x) (map ro2matInv l) mat1.
  Proof.
    intros. unfold rowOps2matInv. rewrite fold_left_map. f_equal.
    extensionality M. extensionality op. rewrite mmul_ro2matInv_l. auto.
  Qed.

  (** rowOps2matInv l * rowOps2mat l = mat1 *)
  Lemma mmul_rowOps2matInv_rowOps2mat_eq1 : forall {n} (l : list (@RowOp n)),
      Forall roValid l -> rowOps2matInv l * rowOps2mat l = mat1.
  Proof.
    intros.
    (* convert to mmul *)
    rewrite rowOps2mat_eq. rewrite rowOps2matInv_eq. rewrite <- fold_left_rev_right.
    (* If we assume l = a1;a2;a3, and denoted that
            map ro2matInv l       = a1';a2';a3'
            rev (map ro2matInv l) = a3';a2';a1'
            map ro2mat l          = a1;a2;a3,
       then the Goal is: (a3'*a2'*a1'*mat1) * (a1*a2*a3*mat1) = mat1 *)
    induction l; simpl. apply mmul_1_l.
    (* Convert 'ro2matInv a' to second items of matrix multiplication *)
    replace (fold_right mmul mat1 (rev (map ro2matInv l) ++ [ro2matInv a]))
      with ((fold_right mmul mat1 (rev (map ro2matInv l))) * (ro2matInv a)).
    2: {
      (* (a3'*a2'*a1'*mat1)*a' = (a3'*a2'*a1'*a')*mat1 *)
      remember (rev (map ro2matInv l)). remember (ro2matInv a).
      clear Heqv IHl Heql0.
      induction l0; simpl. rewrite mmul_1_l, mmul_1_r; auto.
      rewrite mmul_assoc. f_equal. rewrite IHl0. auto. }
    (* Now, eliminate the middle two items *)
    rewrite mmul_assoc. rewrite <- (mmul_assoc (ro2matInv a)).
    rewrite mmul_ro2matInv_ro2mat. rewrite mmul_1_l. apply IHl.
    inversion H; auto. inversion H; auto.
  Qed.

  (** rowOps2mat l * rowOps2matInv l = mat1 *)
  Lemma mmul_rowOps2mat_rowOps2matInv_eq1 : forall {n} (l : list (@RowOp n)),
      Forall roValid l -> rowOps2mat l * rowOps2matInv l = mat1.
  Proof.
    intros.
    (* convert to mmul *)
    rewrite rowOps2mat_eq. rewrite rowOps2matInv_eq. rewrite <- fold_left_rev_right.
    (* If we assume l = a1;a2;a3, and denoted that
            map ro2matInv l       = a1';a2';a3'
            rev (map ro2matInv l) = a3';a2';a1'
            map ro2mat l          = a1;a2;a3,
       then the Goal is: (a1*a2*a3*mat1) (a3'*a2'*a1'*mat1) = mat1 *)
    induction l; simpl. apply mmul_1_l.
    (* Convert 'ro2matInv a' to last items of matrix multiplication *)
    replace (fold_right mmul mat1 (rev (map ro2matInv l) ++ [ro2matInv a]))
      with ((fold_right mmul mat1 (rev (map ro2matInv l))) * (ro2matInv a)).
    2: {
      (* (a3'*a2'*a1'*mat1)*a' = (a3'*a2'*a1'*a')*mat1 *)
      remember (rev (map ro2matInv l)). remember (ro2matInv a).
      clear Heqv IHl Heql0.
      induction l0; simpl. rewrite mmul_1_l, mmul_1_r; auto.
      rewrite mmul_assoc. f_equal. rewrite IHl0. auto. }
    (* Now, eliminate the middle two items *)
    rewrite <- !mmul_assoc. rewrite (mmul_assoc (ro2mat a)). rewrite IHl.
    rewrite mmul_1_r. rewrite mmul_ro2mat_ro2matInv. auto.
    inversion H; auto. inversion H; auto.
  Qed.

  (** rowOps2mat l * M = N -> rowOps2matInv l * N = M *)
  Lemma rowOps2mat_imply_rowOps2matInv : forall {n} (l : list RowOp) (M N : smat (S n)),
      Forall roValid l -> (rowOps2mat l) * M = N -> (rowOps2matInv l) * N = M.
  Proof.
    intros. rewrite <- H0. rewrite <- mmul_assoc.
    rewrite mmul_rowOps2matInv_rowOps2mat_eq1; auto. rewrite mmul_1_l. auto.
  Qed.

  (** rowOps2matInv l * M = N -> rowOps2mat l * N = M *)
  Lemma rowOps2matInv_imply_rowOps2mat : forall {n} (l : list RowOp) (M N : smat (S n)),
      Forall roValid l -> (rowOps2matInv l) * M = N -> (rowOps2mat l) * N = M.
  Proof.
    intros. rewrite <- H0. rewrite <- mmul_assoc.
    rewrite mmul_rowOps2mat_rowOps2matInv_eq1; auto. rewrite mmul_1_l. auto.
  Qed.

  (** (l1 * l2 * ... * ln * 1) * a = l1 * l2 * ... * ln * (a * 1) *)
  Lemma fold_right_mmul_rebase : forall {n} (l : list (smat n)) (a : smat n),
      fold_right mmul mat1 l * a = fold_right mmul a l.
  Proof.
    intros n. induction l; intros; simpl. rewrite mmul_1_l; auto.
    rewrite mmul_assoc. rewrite IHl. auto.
  Qed.

  (** rowOps2matInv (l1 ++ l2) = rowOps2matInv l2 * rowOps2matInv l1 *)
  Theorem rowOps2matInv_app : forall {n} (l1 l2 : list (@RowOp n)),
      rowOps2matInv (l1 ++ l2) = rowOps2matInv l2 * rowOps2matInv l1.
  Proof.
    intros n. unfold rowOps2matInv.
    remember (fun (M : smat (S n)) (op : RowOp) =>
                match op with
                | ROnop => M
                | ROswap i j => mrowSwap i j M
                | ROscale i c => mrowScale i (/ c) M
                | ROadd i j c => mrowAdd i j (- c) M
                end) as f.
    (* by induction on l2 is easier *)
    intros l1 l2. revert l1. induction l2.
    - intros. simpl. rewrite app_nil_r. rewrite mmul_1_l; auto.
    - intros. simpl.
      replace (l1 ++ a :: l2)%list with ((l1 ++ [a]) ++ l2)%list;
        [|rewrite <- app_assoc; auto].
      rewrite IHl2. rewrite fold_left_app; simpl.
      (* Assume: l1 = [b1;b2], l2 = [c1;c2], then
         l1++l2 = [b1;b2;c1;c2]
         f mat1 a                        = Ta*1
         fold_left f l2 mat1             = Tc2*Tc1*1
         fold_left f l2 (f mat1 a)       = Tc2*Tc1*Ta*1
         fold_left f l1 mat1             = Tb2*Tb1*1
         f (fold_left f l1 mat1) a       = Ta*Tb2*Tb1*1
      The goal is:
         (Tc2*Tc1*1)*(Ta*Tb2*Tb1*1) = (Tc2*Tc1*Ta*1)*(Tb2*Tb1*1) *)
      replace (f (fold_left f l1 mat1) a)
        with (ro2matInv a * (fold_left f l1 mat1)).
      2:{ rewrite mmul_ro2matInv_l. rewrite Heqf; auto. }
      replace (fold_left f l2 (f mat1 a))
        with ((fold_left f l2 mat1) * ro2matInv a).
      2:{
        (* a difficulty proof *)
        clear IHl2. rename l2 into l. clear l1.
        assert (f = fun (M : smat (S n)) op => ro2matInv op * M).
        { rewrite Heqf. unfold ro2matInv.
          extensionality M. extensionality op. destruct op.
          rewrite mmul_1_l; auto.
          rewrite mrowSwap_eq; auto.
          rewrite mrowScale_eq; auto.
          rewrite mrowAdd_eq; auto. }
        (* op ==> 矩阵乘法 *)
        rewrite H.
        rewrite <- (fold_left_map l (fun x y => y * x) ro2matInv).
        rewrite <- (fold_left_map l (fun x y => y * x) ro2matInv).
        (* “交换的矩阵乘法” ==> 正常的矩阵转换 *)
        rewrite <- fold_left_rev_right.
        rewrite <- fold_left_rev_right.
        remember (rev (map ro2matInv l)) as L.
        rewrite mmul_1_r.
        remember (ro2matInv a) as b.
        (* (l1*l2*l3*1)*b = l1*l2*l3*(b*1) *)
        rewrite fold_right_mmul_rebase. auto. }
      rewrite mmul_assoc. auto.
  Qed.

  Inductive MRT {r c} : mat r c -> mat r c -> Prop :=
    | MRTswap (i j : fin r) : forall M : mat r c, MRT M (mrowSwap i j M)
    | MRTscale (i : fin r) (K : tA) : forall M : mat r c, K <> 0 -> MRT M (mrowScale i K M)
    | MRTadd (i j : fin r) (K : tA) : forall M : mat r c, i <> j -> MRT M (mrowAdd i j K M)
    | MRTrefl : forall M : mat r c, MRT M M
    | MRTtrans : forall M1 M2 M3 : mat r c, MRT M1 M2 -> MRT M2 M3 -> MRT M1 M3.

  Lemma MRTsym :
    forall {r c} (M N : mat (S r) (S c)),
      MRT M N -> MRT N M.
  Proof. 
    intros. induction H.
    - replace M with (mrowSwap i j (mrowSwap i j M)) at 2.
      apply MRTswap. rewrite !mrowSwap_eq. rewrite <- !mmul_assoc.
      replace (mmul (mrowSwapM i j) (mrowSwapM i j)) with (@mat1 (S r)).
      rewrite mmul_1_l; auto. symmetry. apply mmul_mrowSwapM_mrowSwapM.
    - replace M with (mrowScale i (/ K) ((mrowScale i K M))) at 2.
      apply MRTscale. apply field_inv_neq0_if_neq0; auto.
      rewrite !mrowScale_eq. rewrite <- !mmul_assoc.
      replace (mmul (mrowScaleM i (/ K)) (mrowScaleM i K)) with (@mat1 (S r)).
      rewrite mmul_1_l; auto. symmetry. apply mmul_mrowScaleM_mrowScaleM'; auto.
    - replace M with (mrowAdd i j (- K) (mrowAdd i j K M)) at 2.
      apply MRTadd; auto. rewrite !mrowAdd_eq. rewrite <- !mmul_assoc.
      replace (mmul (mrowAddM i j (- K)) (mrowAddM i j K)) with (@mat1 (S r)).
      rewrite mmul_1_l; auto. symmetry. apply mmul_mrowAddM_mrowAddM'; auto.
    - apply MRTrefl.
    - apply MRTtrans with M2; auto.
  Qed.  


  Lemma MRT_RowOp :
    forall {r c} (M N : mat (S r) (S c)),
    MRT M N <-> 
      (exists (l : list (@RowOp r)), Forall roValid l /\ mmul (rowOps2mat l) M = N).
  Proof.
    split; intros.
    - induction H.
      + exists [ROswap i j]. split. apply Forall_cons; try easy.
        simpl. symmetry; apply mrowSwap_mat1.
      + exists [ROscale i K]. split. apply Forall_cons; try easy.
        simpl. symmetry; apply mrowScale_mat1.
      + exists [ROadd i j K]. split. apply Forall_cons; try easy.
        simpl. symmetry; apply mrowAdd_mat1.
      + exists [ROnop]. split. apply Forall_cons; try easy.
        simpl. Search (mmul mat1). apply mmul_1_l.
      + destruct IHMRT1 as [l1 [HA HB]]. destruct IHMRT2 as [l2 [HA' HB']].
        exists (l2 ++ l1)%list. split. apply Forall_app; split; auto.
        rewrite rowOps2mat_app. rewrite <- HB'. rewrite <- HB. apply mmul_assoc. 
    - destruct H as [l [HA HB]]. generalize dependent N. induction l; intros.
      + simpl in HB. rewrite mmul_1_l in HB; subst. apply MRTrefl.
      + apply Forall_cons_iff in HA. destruct HA.
        replace (a :: l) with ([a] ++ l)%list in HB by auto.
        rewrite rowOps2mat_app in HB. rewrite mmul_assoc in HB.
        specialize IHl with (mmul (rowOps2mat l) M).
        apply IHl in H0; auto. clear IHl.
        simpl rowOps2mat in HB. destruct a; rewrite <- HB; simpl in H.
        * rewrite mmul_1_l. auto.
        * eapply MRTtrans. apply H0. rewrite <- mrowSwap_mat1. apply MRTswap.
        * eapply MRTtrans. apply H0. rewrite <- mrowScale_mat1. apply MRTscale. auto.
        * eapply MRTtrans. apply H0. rewrite <- mrowAdd_mat1. apply MRTadd. auto. 
  Qed.
  

End Row_Trans.
(* 
Section test.

Context {tA : Type}.
Variable (Azero : tA).
Variable (Aadd : tA -> tA -> tA).
Notation mat0  := (@mat0 tA Azero ).
Notation vfoldl := (@vfoldl _ _  (fin0)).


Definition vseq (n : nat):  @vec 'I_n n.
Proof.
  destruct n. intro i. destruct (fin0_False i).
  intro i. exact i.
Defined.

Record coo_matrix:= {
  coo_row : nat; coo_col : nat;
  coo_list : list ('I_(coo_row) * 'I_(coo_col) * tA);
}.

Definition coo2ff (M : coo_matrix) : @mat tA M.(coo_row) M.(coo_col) :=
  fold_left (fun M' a =>
    let '(x, y, val) := a in mset M' (Aadd val M'.[x].[y]) x y)
  M.(coo_list) mat0.

Record csr_matrix:= {
  csr_row : nat; csr_col : nat; csr_n : nat;
  csr_vals : @vec tA csr_n;
  csr_rowptr : @vec 'I_(S csr_n) (S csr_row); csr_colind : @vec 'I_(csr_col) csr_n;
  csr_con1 : csr_rowptr #0 = #0; csr_con2 : csr_rowptr #csr_row = #csr_n;
  csr_con3 : forall i : 'I_(csr_row), csr_rowptr (fSuccRange i) <= csr_rowptr (fSuccRangeS i)
  }.


Lemma csr2ff_aux : forall a b c d : nat,
  a + d <= c -> b < d -> a + b < c.
Proof. intros. lia. Qed.

Lemma csr2ff_aux' : forall a b : nat,
  a <= b -> a + (b - a) = b.
Proof. intros. lia. Qed.

Definition csr2ff (M : csr_matrix) : @mat tA M.(csr_row) M.(csr_col).
Proof.
  destruct (M.(csr_row)) as [|csr_row'] eqn : Er. intros i j. destruct (fin0_False i).
  destruct (M.(csr_col)) as [|csr_col'] eqn : El. intros i j. destruct (fin0_False j).
  eapply vfoldl.
  - exact (vseq (S csr_row')).
  - exact (mat0).
  - intros M' i. destruct i as [i Ei]. assert (Ei': i < csr_row M). 
    {rewrite Er. auto. } pose proof (nat2fin i Ei') as i'.
    destruct ((M.(csr_rowptr).[fSuccRangeS i'] - M.(csr_rowptr).[fSuccRange i'])%nat) as [|num] eqn : E'. 
    exact (M'). eapply vfoldl.
    + exact (vseq (S num)). + exact (M').
    + intros M'' offset.
    assert ((M.(csr_rowptr).[fSuccRange i'] + offset)%nat < M.(csr_n)). 
    { eapply csr2ff_aux. 2: apply (fin2nat_lt offset). rewrite <- E'.
      erewrite csr2ff_aux'. pose proof (fin2nat_lt (M.(csr_rowptr).[fSuccRangeS i'])).
      apply nat_lt_n_Sm_le. auto. pose proof (M.(csr_con3)). apply H. }
    pose proof (nat2fin ((csr_rowptr M).[fSuccRange i'] + offset)%nat H) as k.
    destruct (M.(csr_colind) k) as [j Ej']. assert (Ej : j < S csr_col').
    { rewrite <- El. auto. } 
    exact (mset M'' (Aadd (M.(csr_vals).[k]) M''.[nat2fin i Ei].[nat2fin j Ej]) (nat2fin i Ei) (nat2fin j Ej)).
Defined.
End test.

Section mytest.
  Let Val : vec 2 := l2v 0 [1;1].
  Let Row : @vec 'I_3 3 := l2v fin0 [#0; #1; #2].
  Let Col : @vec 'I_2 2 := l2v fin0 [#0; #1].

  Axiom Con1 : Row #0 = #0.
  Axiom Con2 : Row #2 = #2.
  Axiom Con3 : forall i : 'I_2, Row (fSuccRange i) <= Row (fSuccRangeS i).

Example csr_example : csr_matrix :=
  {|
    csr_row := 2; csr_col := 2; csr_n := 2;
    csr_vals := Val; csr_rowptr := Row; csr_colind := Col;
    csr_con1 := Con1; csr_con2 := Con2; csr_con3 := Con3; |}.

  Notation csr2ff := (@csr2ff nat 0 add).
  
  Let FF:= csr2ff csr_example.

  Compute m2l(FF).


  Record csr_matrix:= {






Definition csr2ff (M : csr_matrix) : @mat tA M.(csr_row) M.(csr_col) :=
  match M.(csr_row), M.(csr_col),  with 
  | 0, _, _ => mat0 | _, 0, _ => mat0 | _, _, 0 => mat0
  | S csr_row', S csr_col', S csr_n' =>
  vfoldl (vseq (S csr_row')) mat0 (fun M' i => 
    match (M.(csr_rowptr).[#(S i)] - M.(csr_rowptr).[#i])%nat with
    | 0 => M'
    | S num => vfoldl (vseq (S num)) M' (fun M'' j =>
      mset M'' Azero i M.(csr_colind).[#0]
    )
    
    end) end.

Check vfoldl.
*)