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

Require Export MatrixRowTrans.

(* ############################################################################ *)
(** * Gauss elimination. *)
Section GaussElim.
  Context `{HField : Field} `{HAeqDec : Dec _ (@eq tA)}.
  Add Field field_inst : (make_field_theory HField).

  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Infix "/" := (fun a b => a * / b) : A_scope.

  Notation veye := (@veye _ Azero Aone).
  Notation vzero := (@vzero _ Azero).
  
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
  
  Notation roValid := (@roValid _ Azero).
  Notation rowOps2mat := (@rowOps2mat _ Aadd 0 Amul 1 _).
  Notation rowOps2matInv := (@rowOps2matInv _ Aadd 0 Aopp Amul 1 Ainv).
  Notation MRT := (@MRT _ Aadd 0 Amul).  

    (* ======================================================================= *)
  (** ** 某列的第一个非零元的行号 *)

  (** 第 j 列的后 x 个元素中的第 1 个非零元的行号。
      eg: 当 x 是`维数` 时，则从第 0 行开始往下查找。 *)
  Fixpoint getcolPivot {r c} (M : mat (S r) (S c)) (x : nat) (j : 'I_(S c))
    : option ('I_(S r)) :=
    match x with
    | O => None
    | S x' =>
        (* x的递归顺序：   x,    x-1, ... ,    1, (0)
           S n-x的顺序：Sn-x, Sn-x+1, ... , Sn-1, (Sn) *)
        if Aeqdec (M #(S r - x) j) 0
        then getcolPivot M x' j
        else Some #(S r - x)
    end.

  Lemma getcolPivot_imply_nonzero :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      getcolPivot M x j = Some i -> M i j <> 0.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct (Aeqdec (M #(r - x) j) 0).
      + apply IHx in H; auto.
      + inv H. auto.
  Qed.
  
  (* 非零元行号 r < S n *)
  Lemma getcolPivot_max :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      getcolPivot M x j = Some i -> i < S r.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. auto.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.
  
  (* 非零元行号 r >= S n - x *)
  Lemma getcolPivot_min :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      getcolPivot M x j = Some i -> i >= S r - x.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. lia.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.

  Lemma getcolPivot_Some  :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (a : 'I_(S r)) (j : 'I_(S c)),
      getcolPivot M x j = Some a <-> 
        (M.[a].[j] <> 0 /\  (S r - x) <= a /\
        (forall (i : 'I_(S r)), (S r -  x) <= i -> i < a ->  M.[i].[j] = 0)).
  Proof.
    induction x; intros; split; intros.
    - simpl in H. inv H.
    - destruct H as [H [H1 H2]]. pose proof (fin2nat_lt a). lia.
    - simpl in H. destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + specialize IHx with (M:=M) (a:=a) (j:=j). rewrite IHx in H.
        destruct H as [H [H1 H2]]. split;[|split]; auto; try lia.
        intros. replace (S r - S x) with (r - x) in H0 by lia.
        destruct (i ??= r - x) as [E'|E'].
        * rewrite <- E' in E. rewrite nat2finS_fin2nat in E. auto.
        * apply H2; fin.
      + inv H. split;[|split]; fin.
    - destruct H as [H [H1 H2]]. simpl. destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + replace (S r - S x) with (r - x) in H1 by lia.
        destruct (a ??= r - x) as [E'|E']; subst.
        * rewrite <- E' in E. rewrite nat2finS_fin2nat in E. destruct (H E).
        * specialize IHx with (M:=M) (a:=a) (j:=j). rewrite IHx.
          split;[|split]; fin. apply H2; fin.
      + replace (S r - S x) with (r - x) in H1 by lia.
        destruct (a ??= r - x) as [E'|E']; subst.
        * f_equal. rewrite <- E'; fin.
        * specialize H2 with (#(r - x) :'I_( S r)). exfalso; apply E.
          apply H2; fin.      
  Qed. 

  Lemma getcolPivot_None :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (j : 'I_(S c)),
      getcolPivot M x j = None <-> 
        forall (i : 'I_(S r)), S r - x <= i ->  M.[i].[j] = 0.
  Proof.
    split; induction x; intros.
    - simpl in H0. pose proof (fin2nat_lt i). lia.
    - simpl in H. destruct (Aeqdec (M #(r - x) j) 0) as [E|E]; try easy.
      replace (S r - S x) with (r - x) in H0 by lia. destruct (i ??= r - x) as [E0|E0].
      + rewrite <- E. f_equal. apply fin2nat_eq_iff; fin.
      + apply IHx; try easy; try lia.
    - simpl; auto.
    - simpl. replace (S r - S x) with (r - x) in H by lia.
      destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + apply IHx; intros. destruct (i ??= r - x) as [E0|E0].
        * rewrite <- E. f_equal. apply fin2nat_eq_iff; fin.
        * apply H. lia.
      + exfalso. apply E. apply H. apply Nat.eq_le_incl. fin.
  Qed.

  Lemma getcolPivot_same_col : 
    forall (x : nat) {r c} (M M': mat (S r) (S c))  (j : 'I_(S c)),
     M&[j] = M'&[j] ->
    getcolPivot M x j = getcolPivot M' x j.
  Proof.
    induction x; intros; auto. simpl.
    replace (M' #(r - x) j) with (M #(r - x) j).
    destruct (Aeqdec (M #(r - x) j) 0) as [E1|E1].
    - apply IHx; intros; easy.
    - auto.
    - assert (M&[j] #(r - x)= M'&[j] #(r - x)) by (rewrite H; fin).
      unfold mcol in H0; auto.
  Qed.

  Lemma getcolPivot_mremoveT :
    forall (x : nat) {r c} (M : mat (S r) (S (S c))) (i : 'I_(S c)),
      getcolPivot (mremovecT M) x i = getcolPivot M x (fSuccRange i).
  Proof.
      induction x; intros; try easy. 
      simpl. replace (M #(r - x) (fSuccRange i)) with (mremovecT M #(r - x) i).
      destruct (Aeqdec (mremovecT M #(r - x) i) 0) as [E|E]; fin.
      unfold mremovecT. rewrite vnth_vmap. rewrite vnth_vremoveT. auto.
  Qed.

  Lemma getcolPivot_neqzero :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      S r - x <= i -> M.[i].[j] <> 0 ->
      exists a : 'I_(S r), getcolPivot M x j = Some a /\ a <= i.
  Proof.
    induction x; intros. 
    - pose proof (fin2nat_lt i); lia.
    - destruct (i ??= r - x) as [E0 | E0].
      + exists i. split; auto. simpl. replace (#(r - x) : 'I_(S r)) with i.
        2 : { apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; fin. }
        destruct (Aeqdec (M i j) 0) as [E1| E1]; auto. 
        rewrite E1 in H0. destruct H0; auto.
      + apply IHx in H0; try lia. destruct H0 as [a [H0 H1]].
        simpl. destruct (Aeqdec (M #(r - x) j) 0) as [E1|E1].
        * exists a; split; auto.
        * exists (#(r - x) : 'I_(S r)). split; auto. rewrite fin2nat_nat2finS; lia.
  Qed.

  Lemma getcolPivot_eq_Some :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (j : 'I_(S c)) (a : 'I_(S r)),
    getcolPivot M x j = Some a <->
    (S r - x <= a /\ M.[a].[j] <> 0 /\ forall i : 'I_(S r), S r - x <= i -> i < a -> M.[i].[j] = 0).
  Proof.
    induction x; intros; split; intros.
    - simpl in H. inv H.
    - destruct H. pose proof (fin2nat_lt a). lia.
    - simpl in H. destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + apply IHx in H. destruct H as [H [H0 H1]]. repeat split; try lia; auto.
        intros. destruct (i ??= r - x) as [E'|E'].
        * replace i with (#(r-x) : 'I_(S r)); auto.
          apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; fin.
        * apply H1; fin.
      + inv H. split;[|split]; auto.
        * rewrite fin2nat_nat2finS; auto. 
          replace (S r- S x) with (r - x) by lia. lia.
        * intros. rewrite fin2nat_nat2finS in H0; lia.
    - destruct H as [H [H1 H2]]. simpl. destruct (a ??= r - x) as [E|E].
      + replace a with (#(r-x) : 'I_(S r)) in *.
        2 :{ apply fin2nat_eq_iff; rewrite fin2nat_nat2finS; lia. }
        destruct (Aeqdec (M #(r - x) j) 0 ) as [E'|E']; auto. contradiction.
      + destruct (Aeqdec (M #(r - x) j) 0)  as [E'|E'].
        * apply IHx; repeat split; try lia; auto.
          intros. apply H2; lia.
        * exfalso. apply E'. apply H2; fin.
  Qed.

   Lemma getcolPivot_eq_None :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (j : 'I_(S c)),
    getcolPivot M x j = None <->
    (forall i : 'I_(S r), S r - x <= i -> M.[i].[j] = 0).
  Proof.
    induction x; intros; split; intros.
    - pose proof (fin2nat_lt i); fin.
    - auto. 
    - replace (S r - S x) with (r - x) in H0 by lia.
      simpl in H. destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + destruct (i ??= r - x) as [E'|E'].
        * replace i with (#(r - x) : 'I_(S r)); auto.
          apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; lia.
      * apply IHx with (i:=i) in H; auto. lia.
      + inv H.
    - simpl. destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + apply IHx; intros. apply H; fin.
      + exfalso. apply E. apply H; fin.
  Qed.    

    (** {a <= b} + {~(a <= b)} *)
  Lemma getcolPivot_dec : 
     forall (x : nat) {r c} (M : mat (S r) (S c)) (j : 'I_(S c)),
     {exists a : 'I_(S r), getcolPivot M x j = Some a } + {getcolPivot M x j = None}.
  Proof.
    induction x; intros.
    - right. auto.
    - simpl. destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + apply IHx.
      + left. exists (#(r - x) : 'I_(S r)). auto.  
  Qed.

  Lemma getcolPivot_same_row : 
    forall (x : nat) {r c} (M M': mat (S r) (S c)) (j : 'I_(S c)),
    M&[j] = M'&[j] ->
    getcolPivot M x j = getcolPivot M' x j.
  Proof.
    induction x; intros; auto. simpl.
    replace (M' #(r - x) j) with (M #(r - x) j).
    destruct (Aeqdec (M #(r - x) j) 0) as [E1|E1]; auto.
    assert (M&[j] #(r - x) = M'&[j] #(r - x)) by (rewrite H; auto).
    unfold mcol in H0. fin.
  Qed.

  (* ======================================================================= *)
  (** ** 某行的第一个非零元的列号 *)

  (** 第 j 列的后 x 个元素中的第 1 个非零元的行号。
      eg: 当 x 是`维数` 时，则从第 0 行开始往下查找。 *)
  Fixpoint getrowPivot {r c} (M : mat (S r) (S c)) (x : nat) (i : 'I_(S r))
    : option ('I_(S c)) :=
    match x with
    | O => None
    | S x' =>
        (* x的递归顺序：   x,    x-1, ... ,    1, (0)
           S n-x的顺序：Sn-x, Sn-x+1, ... , Sn-1, (Sn) *)
        if Aeqdec (M i #(S c - x)) 0
        then getrowPivot M x' i 
        else Some #(S c - x)
    end.

  Lemma getrowPivot_imply_nonzero :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      getrowPivot M x i = Some j -> M i j <> 0.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct (Aeqdec (M i #(c - x)) 0).
      + apply IHx in H; auto.
      + inv H. auto.
  Qed.
  
  (* 非零元列号 j < S n *)
  Lemma getrowPivot_max : 
    forall (x : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      getrowPivot M x i = Some j -> j < S c.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. auto.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.
  
  (* 非零元列号 j >= S c - x *)
  Lemma getrowPivot_min :
    forall (x : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      getrowPivot M x i = Some j -> j >= S c - x.
  Proof.
    induction x; intros.
    - simpl in H. easy.
    - simpl in H. destruct Aeqdec as [E|E].
      + apply IHx in H. lia.
      + inversion H. rewrite fin2nat_nat2finS; lia.
  Qed.

  Lemma getrowPivot_mremoveT :
    forall (x : nat) {r c} (M : mat (S (S r)) (S c)) (i : 'I_(S r)),
      getrowPivot (mremoverT M) x i = getrowPivot M x (fSuccRange i).
  Proof.
      induction x; intros; try easy. 
      simpl. unfold mremoverT; rewrite vnth_vremoveT.
      destruct (Aeqdec (M (fSuccRange i) #(c - x)) 0) eqn : E; 
      [apply IHx|]; easy.
  Qed.


  Lemma getcolPivotNone_getrowPivot :
    forall (x y: nat) {r c} (M : mat (S r) (S c)),
      getcolPivot M x #(c - y) = None ->
        forall (i : 'I_(S r)), S r - x <= i ->
          getrowPivot M (S y) i = getrowPivot M y i.
  Proof.
    intros. rewrite getcolPivot_None in H. simpl.
    destruct (Aeqdec (M i #(c - y)) 0) as [E|E]; try easy.
    exfalso; apply E. apply H; try easy.
  Qed.

  Lemma getrowPivot_neqzero :
    forall (y : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)),
      S c - y <= j -> M.[i].[j] <> 0 ->
      exists a : 'I_(S c), getrowPivot M y i = Some a /\ a <= j.
  Proof.
    induction y; intros. 
    - pose proof (fin2nat_lt j); lia.
    - destruct (j ??= c - y) as [E0 | E0].
      + exists j. split; auto. simpl. replace (#(c - y) : 'I_(S c)) with j.
        2 : { apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; fin. }
        destruct (Aeqdec (M i j) 0) as [E1| E1]; auto. 
        rewrite E1 in H0. destruct H0; auto.
      + apply IHy in H0; try lia. destruct H0 as [a [H0 H1]].
        simpl. destruct (Aeqdec (M i #(c - y)) 0) as [E1|E1].
        * exists a; split; auto.
        * exists (#(c - y) : 'I_(S c)). split; auto. rewrite fin2nat_nat2finS; lia.
  Qed.

  Lemma getrowPivot_eq_Some :
    forall (y : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (a : 'I_(S c)),
    getrowPivot M y i = Some a <->
    (S c - y <= a /\ M.[i].[a] <> 0 /\ forall j : 'I_(S c), S c - y <= j -> j < a -> M.[i].[j] = 0).
  Proof.
    induction y; intros; split; intros.
    - simpl in H. inv H.
    - destruct H. pose proof (fin2nat_lt a). lia.
    - simpl in H. destruct (Aeqdec (M i #(c - y)) 0) as [E|E].
      + apply IHy in H. destruct H as [H [H0 H1]]. repeat split; try lia; auto.
        intros. destruct (j ??= c - y) as [E'|E'].
        * replace j with (#(c-y) : 'I_(S c)); auto.
          apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; fin.
        * apply H1; fin.
      + inv H. split;[|split]; auto.
        * rewrite fin2nat_nat2finS; auto. 
          replace (S c - S y) with (c - y) by lia. lia.
        * intros. rewrite fin2nat_nat2finS in H0; lia.
    - destruct H as [H [H1 H2]]. simpl. destruct (a ??= c - y) as [E|E].
      + replace a with (#(c-y) : 'I_(S c)) in *.
        2 :{ apply fin2nat_eq_iff; rewrite fin2nat_nat2finS; lia. }
        destruct (Aeqdec (M i #(c - y)) 0 ) as [E'|E']; auto. contradiction.
      + destruct (Aeqdec (M i #(c - y)) 0)  as [E'|E'].
        * apply IHy; repeat split; try lia; auto.
          intros. apply H2; lia.
        * exfalso. apply E'. apply H2; fin.
  Qed.

   Lemma getrowPivot_eq_None :
    forall (y : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)),
    getrowPivot M y i = None <->
    (forall j : 'I_(S c), S c - y <= j -> M.[i].[j] = 0).
  Proof.
    induction y; intros; split; intros.
    - pose proof (fin2nat_lt j); fin.
    - auto. 
    - replace (S c - S y) with (c - y) in H0 by lia.
      simpl in H. destruct (Aeqdec (M i #(c - y)) 0) as [E|E].
      + destruct (j ??= c - y) as [E'|E'].
        * replace j with (#(c - y) : 'I_(S c)); auto.
          apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; lia.
        * apply IHy with (j:=j) in H; auto. lia.
      + inv H.
    - simpl. destruct (Aeqdec (M i #(c - y)) 0) as [E|E].
      + apply IHy; intros. apply H; fin.
      + exfalso. apply E. apply H; fin.
  Qed.    

    (** {a <= b} + {~(a <= b)} *)
  Lemma getrowPivot_dec : 
     forall (y : nat) {r c} (M : mat (S r) (S c)) (i : 'I_(S r)),
     {exists a : 'I_(S c), getrowPivot M y i = Some a } + {getrowPivot M y i = None}.
  Proof.
    induction y; intros.
    - right. auto.
    - simpl. destruct (Aeqdec (M i #(c - y)) 0) as [E|E].
      + apply IHy.
      + left. exists (#(c - y) : 'I_(S c)). auto.  
  Qed.

  Lemma getrowPivot_same_row : 
    forall (y : nat) {r c} (M M': mat (S r) (S c)) (i : 'I_(S r)),
    M.[i] = M'.[i] ->
    getrowPivot M y i = getrowPivot M' y i.
  Proof.
    induction y; intros; auto. simpl.
    replace (M' i) with (M i) by auto.
    destruct (Aeqdec (M i #(c - y)) 0) as [E1|E1]; auto.
  Qed.

    (* ======================================================================= *)
  (** ** 矩阵形状的谓词 *)

  (** 方阵 M 的前 x 列的左下角(不含对角线)是 0。当 x = n 时，整个矩阵左下角是 0 *)
  Definition mLeftLowerZeros {n} (M : smat n) (x : nat) : Prop :=
    forall (i j : 'I_n), j < x -> j < i -> M.[i].[j] = 0.

  Lemma mLeftLowerZeros_less : forall {n} (M : smat (S n)) (x : nat),
      mLeftLowerZeros M (S x) -> mLeftLowerZeros M x.
  Proof. intros. hnf in *; intros. rewrite H; auto. Qed.
  
  Lemma mLeftLowerZeros_S : forall {n} (M : smat (S n)) (x : nat),
      (forall (i : 'I_(S n)), x < i -> M i #x = 0) ->
      mLeftLowerZeros M x -> mLeftLowerZeros M (S x).
  Proof.
    intros. hnf in *; intros. destruct (x ??= j).
    - assert (j = #x). rewrite e. rewrite nat2finS_fin2nat; auto.
      rewrite H3. rewrite H; auto. lia.
    - rewrite H0; auto. lia.
  Qed.

  
  (** 方阵 M 是上三角矩阵（即，左下角都是0）  *)
  Definition mUpperTrig {n} (M : smat n) : Prop :=
    mLeftLowerZeros M n.
  
  Lemma mat1_mLeftLowerZeros : forall {n}, mLeftLowerZeros (@mat1 n) n.
  Proof.
    intros. hnf. intros. rewrite mnth_mat1_diff; auto.
    assert (fin2nat i <> j); try lia. fin.
  Qed.
  
  Lemma mat1_mUpperTrig : forall {n}, mUpperTrig (@mat1 n).
  Proof. intros. unfold mUpperTrig. apply mat1_mLeftLowerZeros. Qed.

  (** 方阵 M 的前 x 行/列的对角线都是 1。当 x=n 时，整个矩阵的对角线是 1 *)
  Definition mDiagonalOne {n} (M : smat n) (x : nat) : Prop :=
    forall (i : 'I_n), i < x -> M i i = 1.
  
  Lemma mat1_mDiagonalOne : forall {n}, mDiagonalOne (@mat1 n) n.
  Proof. intros. hnf; intros. rewrite mnth_mat1_same; auto. Qed.

  (** 方阵 M 的对角线都是 1 *)
  Definition mDiagonalOnes {n} (M : smat n) : Prop := mDiagonalOne M n.
  
  Lemma mat1_mDiagonalOnes : forall {n}, mDiagonalOnes (@mat1 n).
  Proof. intros. unfold mDiagonalOnes. apply mat1_mDiagonalOne. Qed.
  
  (** 方阵 M 是单位上三角矩阵（即，左下角全0 + 对角线全1）*)
  Definition mUnitUpperTrig {n} (M : smat n) := 
    mUpperTrig M /\ mDiagonalOnes M.
  
  (** 单位上三角矩阵，任意下面的行的倍数加到上面，仍然是单位上三角矩阵 *)
  Lemma mrowAdd_mUnitUpperTrig : forall {n} (M : smat (S n)) (i j : 'I_(S n)),
      mUnitUpperTrig M ->
      i < j ->
      mUnitUpperTrig (mrowAdd i j (- (M i j))%A M).
  Proof.
    intros. unfold mUnitUpperTrig in *. destruct H. split; hnf in *; intros.
    - unfold mrowAdd; fin. subst.
      rewrite !(H _ j0); auto. ring.
      pose proof (fin2nat_lt j). lia.
    - unfold mrowAdd; fin. fin2nat.
      rewrite H1; auto; fin. rewrite (H _ i); auto. ring.
  Qed.
  
  
  (** 方阵 M 的后 x 列的右上角（不含对角线）全是 0。
      当 x = n 时，整个矩阵右上角是 0 *)
  Definition mRightUpperZeros {n} (M : smat n) (x : nat) : Prop :=
    forall (i j : 'I_n), n - x <= j -> i < j -> M i j = 0.
  
  Lemma mat1_mRightUpperZeros : forall {n}, mRightUpperZeros (@mat1 n) n.
  Proof.
    intros. hnf. intros. rewrite mnth_mat1_diff; auto.
    assert (fin2nat i <> j); try lia. fin.
  Qed.

  (* ******************************************************************* *)
  (** ** 方阵向下消元 *)
  
  (* 将矩阵M的第j列的后 x 行元素变为 0。当 j=#0时，x=n *)
  Fixpoint smElimDown {n} (M : smat (S n)) (x : nat) (j : 'I_(S n))
    : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        (* 递归时 x 从大到小，而 fx 是从小到大 *)
        let fx : 'I_(S n) := #(S n - x) in
        let a : tA := M.[fx].[j] in
        (* 如果 M[S n-x,j] <> 0，则 j 行的 -M[S n-x,j] 倍加到 S n-x 行。要求 M[j,j]=1 *)
        if Aeqdec a 0
        then smElimDown M x' j
        else
          let op1 := ROadd fx j (-a)%A in
          let M1 := mrowAdd fx j (-a)%A M in
          let (l2, M2) := smElimDown M1 x' j in
          ((l2 ++ [op1])%list, M2)
    end.
  
  (** 对 M 向下消元得到 (l, M')，则 l 都是有效的 *)
  Lemma smElimDown_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      x < S n - j -> smElimDown M x j = (l, M') -> Forall roValid l.
  Proof.
    induction x; intros; simpl in *.
    - inversion H0. constructor.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #(n - x) j) 0) as [E|E].
      + apply IHx in H0; auto. lia.
      + destruct smElimDown as [l2 M2] eqn: T2.
        apply IHx in T2; try lia. inversion H0.
        apply Forall_app. split; auto. repeat constructor. hnf. intro.
        destruct j.
        assert (n - x = i).
        { erewrite nat2finS_eq in H1. apply fin_eq_iff in H1. auto. }
        fin. subst. destruct (n - x) eqn:H2. fin. fin.
        Unshelve. fin.
  Qed.

  (** 对 M 向下消元得到 (l, M')，则 [l] * M = M' *)
  Lemma smElimDown_eq :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      smElimDown M x j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #(n - x) j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct smElimDown as [l2 M2] eqn: T2.
        apply IHx in T2. inversion H. rewrite <- H2, <- T2.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.

  (* 若M[y,y]=1，则对第y列的 后 x 行向下消元后，前S n - x行的所有元素保持不变 *)
  Lemma smElimDown_keep_former_row :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      smElimDown M x y = (l, M') ->
      M y y = 1 ->
      x < S n - y ->
      (forall i j : 'I_(S n), i < S n - x -> M' i j = M i j).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct Aeqdec as [E|E].
      + apply IHx with (i:=i)(j:=j) in H; auto; try lia.
      + destruct smElimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5. apply IHx with (i:=i)(j:=j) in T2; try lia.
        * rewrite T2. unfold mrowAdd; fin.
        * unfold mrowAdd; fin.
  Qed.
  
  (* 若M[y,y]=1，则对第y列的 后 x 行向下消元后，第 y 列的后x行的所有元素变成 0 *)
  Lemma smElimDown_latter_row_0:
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      smElimDown M x y = (l, M') ->
      M y y = 1 ->
      x < S n - y ->
      (forall i : 'I_(S n), S n - x <= i -> M' i y = 0).
  Proof.
    induction x; intros.
    - pose proof (fin2nat_lt i). lia.
    - simpl in H.
      destruct (Aeqdec (M #(n - x) y) 0) as [E|E].
      + destruct (i ??= n - x) as [E1|E1].
        * apply smElimDown_keep_former_row with (i:=i)(j:=y) in H; auto; try lia.
          subst. rewrite H. rewrite <- E1 in E. rewrite nat2finS_fin2nat in E; auto.
        * apply IHx with (i:=i) in H; auto; try lia.
      + destruct smElimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5.
        replace (S n - S x) with (n - x) in H2 by lia.
        destruct (i ??= n - x) as [E1|E1].
        * apply smElimDown_keep_former_row with (i:=i)(j:=y) in T2; auto; try lia.
          ** rewrite T2. unfold mrowAdd; fin. rewrite H0. rewrite <- E0. fin.
          ** unfold mrowAdd; fin.
        * apply IHx with (i:=i) in T2; auto; try lia. unfold mrowAdd; fin.
  Qed.

  (* 若 M 的前 y 列左下方都是0，则对后 x 行向下消元后，M' 的前 y 列左下方都是0 *)
  Lemma smElimDown_mLowerLeftZeros_aux:
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      smElimDown M x y = (l, M') ->
      mLeftLowerZeros M (y) ->
      x < S n - y ->
      M y y = 1 ->
      mLeftLowerZeros M' (y).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #(n - x) y) 0) as [E|E].
      + apply IHx in H; auto; try lia.
      + destruct smElimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5.
        hnf; intros.
        destruct (x ??< S n - y) as [E1|E1].
        * apply IHx in T2; auto; try lia; clear IHx.
          ** hnf; intros. unfold mrowAdd; fin.
             rewrite !(H0 _ j0); auto. ring.
          ** unfold mrowAdd; fin.
        * apply smElimDown_keep_former_row with (i:=i)(j:=j) in T2; auto; try lia.
  Qed.

  (** 若 M 前 x 列左下是0，则对 M 的后 S n - S x 列消元后的 M' 的前 S x 列左下是 0 *)
  Lemma smElimDown_mLeftLowerZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      smElimDown M (S n - S x) #x = (l, M') ->
      x < S n ->
      M #x #x = 1 ->
      mLeftLowerZeros M x ->
      mLeftLowerZeros M' (S x).
  Proof.
    intros. hnf; intros.
    (* 两种情况：在 x 列，在 x 列左侧 *)
    destruct (j ??= x) as [E|E].
    - apply smElimDown_latter_row_0 with (i:=i) in H; auto; subst; fin.
    - apply smElimDown_mLowerLeftZeros_aux in H; auto; fin.
      rewrite H; auto.
      pose proof (fin2nat_lt j). lia.
  Qed.


  (* ******************************************************************* *)
  (** ** 化为行阶梯形 *)

  (*            (x=3)        (x=4)
   * * * *    * * * *     1 * * *
   * * * *    * 1 * *     0 1 * *
   * * * * => * 0 1 *     0 0 1 *
   * * * *    * 0 0 1     0 0 0 1
     -----------------------------------
     递归时i    3 2 1 (0)   4 3 2 1 (0)
     递归时n-i  1 2 3       0 1 2 3
   *)
  (* 将矩阵M的后 x 行化为单位上三角形。
     参数 x 最大为维数，递归时 x 递减，而 (维数-x) 递增。*)
  Fixpoint sm2REF {n} (M : smat (S n)) (x : nat)
    : option (list RowOp * smat (S n)) :=
    match x with
    | O => Some ([], M)
    | S x' =>
        let j : 'I_(S n) := #(S n - x) in
        (* 找出主元 *)
        match getcolPivot M x j with
        | None => None (* 没有非零元，则该矩阵不可逆 *)
        | Some i =>
            (* 使主元行在当前行 *)
            let (op1, M1) :=
              (if i ??= j       (* 若当前行就是主元行，则不需要交换 *)
               then (ROnop, M)
               else (ROswap j i, mrowSwap j i M)) in
            (* 使主元是 1 *)
            let (op2, M2) :=
              (let c : tA := M1.[j].[j] in
               (ROscale j (/c), mrowScale j (/c) M1)) in
            (* 使主元以下都是 0 *)
            let (l3, M3) := smElimDown M2 x' j in
            (* 递归 *)
            match sm2REF M3 x' with
            | None => None
            | Some (l4, M4) => Some ((l4 ++ l3 ++ [op2; op1])%list, M4)
            end
        end
    end.

  (** 对 M 行变换得到 (l, M')，则 [l] * M = M' *)
  Lemma sm2REF_eq : forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M x = Some (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros.
    - simpl in H. inversion H. simpl. apply mmul_1_l.
    - unfold sm2REF in H; fold (@sm2REF (n)) in H. (* Tips: simpl展开太多 *)
      destruct getcolPivot as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + (* i 就是当前行，不需要换行 *)
        destruct smElimDown as [l3 M3] eqn:T3.
        destruct sm2REF as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4. inversion H. rewrite <- H2, <- T4.
        apply smElimDown_eq in T3. rewrite <- T3.
        rewrite !rowOps2mat_app. simpl. rewrite !mmul_assoc. f_equal. f_equal.
        rewrite <- mrowScale_mmul. rewrite mmul_1_l. auto.
      + (* i 不是当前行，需要换行 *)
        destruct smElimDown as [l3 M3] eqn:T3.
        destruct (sm2REF M3 x) as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4. inversion H. rewrite <- H2, <- T4.
        apply smElimDown_eq in T3. rewrite <- T3.
        rewrite !rowOps2mat_app. simpl. rewrite !mmul_assoc. f_equal. f_equal.
        rewrite <- mrowScale_mmul. rewrite <- mrowSwap_mmul. rewrite mmul_1_l. auto.
  Qed.

  (** M 的前 S n - x 列左下角是0，且将 M 的后 x 行变换上三角得到 (l, M')，
      则 M' 的所有列的左下角是 0 *)
  Lemma sm2REF_mLeftLowerZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M x = Some (l, M') ->
      x <= S n ->
      mLeftLowerZeros M (S n - x) ->
      mLeftLowerZeros M' (S n).
  Proof.
    induction x; intros.
    - simpl in *. inv H. auto.
    - unfold sm2REF in H; fold (@sm2REF n) in H.
      replace (S n - S x) with (n - x) in * by lia.
      destruct getcolPivot as [i|] eqn : Hi; try easy.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + destruct smElimDown as [l3 M3] eqn:T3.
        destruct sm2REF as [[l4 M4]|] eqn:T4; try easy.
        inv H. apply IHx in T4; auto; try lia; clear IHx.
        replace x with (S n - (S (n - x))) in T3 at 4 by lia.
        apply smElimDown_mLeftLowerZeros in T3; try lia.
        * replace (S (n - x)) with (S n - x) in T3 by lia; auto.
        * unfold mrowScale; fin.
          (* 确保元素非零时才能消去除法逆元 *)
          rewrite field_mulInvL; auto.
          apply getcolPivot_imply_nonzero in Hi. rewrite <- E in *. fin.
        * hnf; intros. unfold mrowScale; fin. rewrite (H1 _ j); fin.
      + destruct smElimDown as [l3 M3] eqn:T3.
        destruct sm2REF as [[l4 M4]|] eqn:T4; try easy.
        inv H. apply IHx in T4; auto; try lia; clear IHx.
        replace x with (S n - (S (n - x))) in T3 at 6 by lia.
        apply smElimDown_mLeftLowerZeros in T3; try lia.
        * replace (S (n - x)) with (S n - x) in T3 by lia; auto.
        * unfold mrowScale; fin.
          (* 确保元素非零时才能消去除法逆元 *)
          rewrite field_mulInvL; auto.
          unfold mrowSwap; fin. apply getcolPivot_imply_nonzero in Hi. auto.
        * hnf; intros. unfold mrowScale, mrowSwap; fin.
          ** rewrite (H1 _ j); fin. apply getcolPivot_min in Hi. lia.
          ** rewrite (H1 _ j); fin.
  Qed.

  (** 化行阶梯矩阵得到了上三角矩阵 *)
  Lemma sm2REF_mUpperTrig : forall {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M (S n) = Some (l, M') -> mUpperTrig M'.
  Proof.
    intros. apply sm2REF_mLeftLowerZeros in H; auto.
    hnf; intros. lia.
  Qed.
  
  (** M 的前 S n - x 个对角线元素是1，且将 M 的后 x 行变换上三角得到 (l, M')，
      则 M' 的所有对角线都是1 *)
  Lemma sm2REF_mDiagonalOne :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M x = Some (l, M') ->
      mDiagonalOne M (S n - x) ->
      x <= S n ->
      mDiagonalOne M' (S n).
  Proof.
    induction x; intros.
    - simpl in *. inv H. auto.
    - (* simpl in H. *) (* too much! *)
      unfold sm2REF in H; fold (@sm2REF n) in H.
      destruct getcolPivot as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + destruct smElimDown as [l3 M3] eqn:T3.
        destruct sm2REF as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4; clear IHx; try lia.
        * inversion H; clear H. rewrite <- H4. auto.
        * hnf; intros.
          apply smElimDown_keep_former_row with (i:=i0)(j:=i0) in T3; fin.
          ** rewrite T3. unfold mrowScale; fin.
             *** rewrite <- E0. fin. rewrite field_mulInvL; auto.
                 rewrite <- E0 in *. fin.
                 apply getcolPivot_imply_nonzero in Hi; auto.
                 fin2nat. auto.
             *** rewrite H0; auto. lia.
          ** unfold mrowScale; fin. rewrite field_mulInvL; auto.
             apply getcolPivot_imply_nonzero in Hi. rewrite <- E in *. fin.
      + destruct smElimDown as [l3 M3] eqn:T3.
        destruct sm2REF as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4; clear IHx; try lia.
        * inversion H; clear H. rewrite <- H4. auto.
        * hnf; intros.
          apply smElimDown_keep_former_row with (i:=i0)(j:=i0) in T3; fin.
          ** rewrite T3. unfold mrowScale, mrowSwap; fin.
             *** rewrite <- E0. fin. rewrite field_mulInvL; auto.
                 apply getcolPivot_imply_nonzero in Hi.
                 rewrite <- E0 in *. fin.
             *** subst.
                 pose proof (getcolPivot_max _ _ _ _ Hi).
                 pose proof (getcolPivot_min _ _ _ _ Hi). lia.
             *** assert (i0 < n - x). lia.
                 rewrite H0; auto.
          ** unfold mrowScale, mrowSwap; fin.
             rewrite field_mulInvL; auto.
             apply getcolPivot_imply_nonzero in Hi. auto.
  Qed.
  
  (** 化行阶梯矩阵得到的矩阵的对角线都是 1 *)
  Lemma sm2REF_mDiagonalOnes : forall {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M (S n) = Some (l, M') -> mDiagonalOnes M'.
  Proof.
    intros. unfold mDiagonalOnes. apply sm2REF_mDiagonalOne in H; auto.
    hnf; lia.
  Qed.

  (** 对 M 行变换得到 (l, M')，则 l 都是有效的 *)
  Lemma sm2REF_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      x <= S n -> sm2REF M x = Some (l, M') -> Forall roValid l.
  Proof.
    induction x; intros.
    - simpl in H0. inversion H0. constructor.
    - unfold sm2REF in H0; fold (@sm2REF (n)) in H0.
      destruct getcolPivot as [i|] eqn: Hi; try easy.
      replace (S n - S x) with (n - x) in * by lia.
      (* 根据 i ??= #(n - x) 决定是否需要换行 *)
      destruct (i ??= #(n - x)) as [E|E].
      + (* i 就是当前行，不需要换行 *)
        destruct smElimDown as [l3 M3] eqn:T3.
        destruct sm2REF as [[l4 M4]|] eqn:T4; try easy. inversion H0.
        apply IHx in T4 as T4'.
        apply smElimDown_rowOpValid in T3.
        apply Forall_app. split; auto.
        apply Forall_app. split; auto.
        repeat constructor. unfold roValid.
        apply field_inv_neq0_iff.
        apply getcolPivot_imply_nonzero in Hi. fin2nat. auto. fin. fin.
      + (* i 不是当前行，需要换行 *)
        destruct smElimDown as [l3 M3] eqn:T3.
        destruct (sm2REF M3 x) as [[l4 M4]|] eqn:T4; try easy.
        apply IHx in T4 as T4'. inversion H0.
        apply smElimDown_rowOpValid in T3.
        apply Forall_app. split; auto.
        apply Forall_app. split; auto.
        repeat constructor. unfold roValid.
        apply field_inv_neq0_iff. unfold mrowSwap. fin.
        apply getcolPivot_imply_nonzero in Hi. auto. fin. fin.
  Qed.

  (** 对 M 行变换得到 (l, M')，则 [l]' * M' = M *)
  Lemma sm2REF_eq_inv :  forall {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M (S n) = Some (l, M')  -> rowOps2matInv l * M' = M.
  Proof.
    intros. apply sm2REF_eq in H as H'. rewrite <- H'.
    rewrite <- mmul_assoc. rewrite mmul_rowOps2matInv_rowOps2mat_eq1.
    rewrite mmul_1_l; auto.
    apply sm2REF_rowOpValid in H. auto. lia.
  Qed.
  
  (** 化行阶梯矩阵得到的矩阵是单位上三角矩阵 *)
  Lemma sm2REF_mUnitUpperTrig : forall {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M (S n) = Some (l, M') -> mUnitUpperTrig M'.
  Proof.
    intros. hnf. split.
    apply sm2REF_mUpperTrig in H; auto.
    apply sm2REF_mDiagonalOnes in H; auto.
  Qed.

  (** 化行阶梯形满足乘法不变式，并且结果矩阵是规范的上三角矩阵 *)
  Theorem sm2REF_spec :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2REF M (S n) = Some (l, M') ->
      (rowOps2mat l * M = M') /\ mUnitUpperTrig M'.
  Proof.
    intros. split.
    apply sm2REF_eq in H; auto.
    apply sm2REF_mUnitUpperTrig in H; auto.
  Qed.


  (* ******************************************************************* *)
  (** ** 方阵向上消元 *)
  
  (* 将矩阵M的第 j 列的前 x 行元素变为 0。当 j=#(S n)时，x=S n *)
  Fixpoint smElimUp {n} (M : smat (S n)) (x : nat) (j : 'I_(S n))
    : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        let fx : 'I_(S n) := #x' in
        let a : tA := (M.[fx].[j]) in
        (* 如果 M[x',j] <> 0，则 j 行的 -M[x',j] 倍加到 x' 行。要求 M[j,j]=1 *)
        if Aeqdec a 0
        then smElimUp M x' j
        else
          let (op1, M1) := (ROadd fx j (-a)%A, mrowAdd fx j (-a)%A M) in
          let (l2, M2) := smElimUp M1 x' j in
          ((l2 ++ [op1])%list, M2)
    end.

  (** 对 M 向上消元得到 (l, M')，则 [l] * M = M' *)
  Lemma smElimUp_eq :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      smElimUp M x j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct smElimUp as [l2 M2] eqn:T2.
        apply IHx in T2. inv H.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.
  
  (** 对 M 向上消元得到 (l, M')，则 l 都是有效的 *)
  Lemma smElimUp_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (j : 'I_(S n)) (l : list RowOp),
      x <= j ->     (* 前 x 行，行号不超过 j *)
      smElimUp M x j = (l, M') -> Forall roValid l.
  Proof.
    induction x; intros; simpl in *.
    - inversion H0. constructor.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H0; auto. fin.
      + destruct smElimUp as [l2 M2] eqn:T2.
        apply IHx in T2; fin. inv H0.
        apply Forall_app. split; auto. repeat constructor. hnf. intros.
        rewrite <- H0 in H.
        rewrite fin2nat_nat2finS in H; fin.
        pose proof (fin2nat_lt j). fin.
  Qed.

  (** 对 M 向上消元保持单位上三角矩阵 *)
  Lemma smElimUp_mUnitUpperTrig :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (j : 'I_(S n)),
      smElimUp M x j = (l, M') ->
      x <= j ->     (* 前 x 行，行号不超过 j *)
      mUnitUpperTrig M -> mUnitUpperTrig M'.
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H; auto; try lia.
      + destruct smElimUp as [l2 M2] eqn: T2. inv H.
        apply IHx in T2; auto; try lia.
        apply mrowAdd_mUnitUpperTrig; auto. fin.
        pose proof (fin2nat_lt j). lia.
  Qed.

  (* 上消元时，x 行及以下的行保持不变 *)
  Lemma smElimUp_keep_lower_rows :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      smElimUp M x y = (l, M') ->
      x <= y ->     (* 前 x 行，行号不超过 y *)
      (forall i j : 'I_(S n), x <= i -> M' i j = M i j).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct (Aeqdec (M #x y) 0) as [E|E].
      + apply IHx with (i:=i)(j:=j) in H; auto; try lia.
      + destruct smElimUp as [l2 M2] eqn: T2. inv H.
        apply IHx with (i:=i)(j:=j) in T2; auto; try lia.
        rewrite T2. unfold mrowAdd; fin.
        pose proof (fin2nat_lt y). lia.
  Qed.
  
  (* 上消元后该列上方元素为 0 *)
  Lemma smElimUp_upper_rows_0 :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      smElimUp M x y = (l, M') ->
      mUnitUpperTrig M ->
      x <= y ->     (* 前 x 行，行号不超过 y *)
      (forall i : 'I_(S n), i < x -> M' i y = 0).
  Proof.
    induction x; intros; try lia.
    simpl in H. hnf in H0. destruct H0 as [H00 H01].
    destruct (Aeqdec (M #x y) 0) as [E|E].
    - (* i 在当前列 x，或者 i 小于 x *)
      destruct (x ??= i) as [E1|E1].
      + apply smElimUp_keep_lower_rows with (i:=i)(j:=y) in H; try lia.
        rewrite H. subst. fin.
      + apply IHx with (i:=i) in H; auto; try lia. split; auto.
    - destruct smElimUp as [l2 M2] eqn: T2. inv H.
      (* i 在当前列 x，或者 i 小于 x *)
      destruct (x ??= i) as [E1|E1].
      + rewrite E1 in *.
        apply smElimUp_keep_lower_rows with (i:=i)(j:=y) in T2; try lia. rewrite T2.
        unfold mrowAdd; fin. rewrite H01; auto; try lia; fin.
      + apply IHx with (i:=i) in T2; auto; try lia.
        apply mrowAdd_mUnitUpperTrig; auto. split; auto.
        fin. pose proof (fin2nat_lt y). lia.
  Qed.

  (** 若 M 的后 L 列的右上角都是 0，则上消元后，M' 的后 L 列的右上角都是 0 *)
  Lemma smElimUp_mUpperRightZeros_aux :
    forall (x L : nat) {n} (M M' : smat (S n)) (l : list RowOp) (y : 'I_(S n)),
      smElimUp M x y = (l, M') ->
      x <= y ->
      L < S n - y ->
      mUnitUpperTrig M ->
      mRightUpperZeros M L ->
      mRightUpperZeros M' L.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    simpl in H.
    destruct (Aeqdec (M #x y) 0) as [E|E].
    - hnf; intros.
      apply IHx with (L:=L) in H; auto; try lia.
    - destruct smElimUp as [l2 M2] eqn: T2. inv H.
      hnf; intros.
      apply IHx with (L:=L) in T2; auto; try lia.
      + apply mrowAdd_mUnitUpperTrig; auto. fin.
      + hnf; intros. unfold mrowAdd; fin.
        rewrite !(H3 _ j0); try lia. ring.
  Qed.
  
  (** 若 M 的后 (S n - S y) 列的右上角都是 0，则上消元后，S n - y 列的右上角都是 0 *)
  Lemma smElimUp_mUpperRightZeros:
    forall {n} (M M' : smat (S n)) (l : list RowOp) (y : nat),
      smElimUp M y #y = (l, M') ->
      y < S n ->
      mUnitUpperTrig M ->
      mRightUpperZeros M (S n - S y) ->
      mRightUpperZeros M' (S n - y).
  Proof.
    intros. hnf; intros.
    replace (S n - (S n - y)) with y in H3 by lia.
    destruct (j ??= y) as [E|E].
    - subst. apply smElimUp_upper_rows_0 with (i:=i) in H; auto; fin.
    - apply smElimUp_mUpperRightZeros_aux with (L:=S n - S y) in H; auto; fin.
      rewrite H; auto. lia.
  Qed.
  

  (* ******************************************************************* *)
  (** ** 最简行阶梯形矩阵 *)

  (* 将矩阵 M 的前 x 行(列)化为行最简阶梯形。当 x 为 S n 时表示整个矩阵 *)
  Fixpoint sm2RREF {n} (M : smat (S n)) (x : nat) : list RowOp * smat (S n) :=
    match x with
    | O => ([], M)
    | S x' =>
        let fx : 'I_(S n) := #x' in
        let (l1, M1) := smElimUp M x' fx in
        let (l2, M2) := sm2RREF M1 x' in
        ((l2 ++ l1)%list, M2)
    end.

  (** 对 M 最简行变换得到 (l, M')，则 [l] * M = M' *)
  Lemma sm2RREF_eq : forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2RREF M x = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - destruct smElimUp as [l1 M1] eqn : T1.
      destruct sm2RREF as [l2 M2] eqn : T2.
      apply IHx in T2. inv H.
      apply smElimUp_eq in T1. rewrite <- T1.
      rewrite rowOps2mat_app. apply mmul_assoc.
  Qed.

  (* sm2RREF 保持上三角 *)
  Lemma sm2RREF_mUnitUpperTrig :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2RREF M x = (l, M') ->
      x <= S n ->
      mUnitUpperTrig M ->
      mUnitUpperTrig M'.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct smElimUp as [l1 M1] eqn : T1.
    destruct sm2RREF as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    apply smElimUp_mUnitUpperTrig in T1; auto. fin.
  Qed.
  
  (** 若 M 的 后 S n - x 列的右上角都是0，则对 M 最简行变换得到的 M' 的右上角都是0 *)
  Lemma sm2RREF_mRightUpperZeros :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2RREF M x = (l, M') ->
      x <= S n ->
      mUnitUpperTrig M ->
      mRightUpperZeros M (S n - x) ->
      mRightUpperZeros M' (S n).
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct smElimUp as [l1 M1] eqn : T1.
    destruct sm2RREF as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    - apply smElimUp_mUnitUpperTrig in T1; auto. fin.
    - apply smElimUp_mUpperRightZeros in T1; auto.
  Qed.

  (** 对 M 向下消元得到 (l, M')，则 l 都是有效的 *)
  Lemma sm2RREF_rowOpValid :
    forall (x : nat) {n} (M M' : smat (S n)) (l : list RowOp),
      sm2RREF M x = (l, M') -> x <= S n -> Forall roValid l.
  Proof.
    induction x; intros; simpl in H. inv H; auto.
    destruct smElimUp as [l1 M1] eqn : T1.
    destruct sm2RREF as [l2 M2] eqn : T2. inv H.
    apply IHx in T2; auto; try lia.
    apply smElimUp_rowOpValid in T1 as T1'; fin.
    apply Forall_app. split; auto.
  Qed.
  
  (** 对 M 最简行变换得到 (l, M')，则 [l]' * M' = M *)
  Lemma sm2RREF_eq_inv : forall {n} (M M' : smat (S n)) (l : list RowOp),
      sm2RREF M (S n) = (l, M') -> rowOps2matInv l * M' = M.
  Proof.
    intros. apply sm2RREF_eq in H as H'. rewrite <- H'.
    rewrite <- mmul_assoc. rewrite mmul_rowOps2matInv_rowOps2mat_eq1.
    rewrite mmul_1_l; auto.
    apply sm2RREF_rowOpValid in H; fin.
  Qed.
  
  (** 对 M 最简行变换得到 (l, M')，则 M' 是单位阵 *)
  Lemma sm2RREF_mat1 : forall {n} (M M' : smat (S n)) (l : list RowOp),
      sm2RREF M (S n) = (l, M') ->
      mUnitUpperTrig M -> M' = mat1.
  Proof.
    intros. apply meq_iff_mnth; intros. 
    (* 分别处理：左下角、对角线、右上角 *)
    destruct (j ??< i).
    - (* 左下角 *)
      rewrite mat1_mLeftLowerZeros; auto; fin.
      apply sm2RREF_mUnitUpperTrig in H; auto.
      hnf in H. destruct H. rewrite H; auto; fin.
    - destruct (j ??= i) as [E|E].
      + (* 对角线 *)
        apply sm2RREF_mUnitUpperTrig in H; auto. fin2nat.
        rewrite mat1_mDiagonalOne; fin.
        hnf in H. destruct H. rewrite H1; auto; fin.
      + (* 右上角 *)
        assert (i < j) by lia.
        rewrite mat1_mRightUpperZeros; auto; fin.
        apply sm2RREF_mRightUpperZeros in H; auto; fin.
        * rewrite H; auto; try lia.
        * hnf; intros. pose proof (fin2nat_lt j0). lia.
  Qed.


  (* ******************************************************************* *)
  (* ******************************************************************* *)

  (* ******************************************************************* *)
  (** * 一般矩阵谓词 *)
  
  (** ** 行阶梯行 *)
  
  (** 行首元判断次序，后者若无首元恒成立 *)
  Definition rpivotlt {n} (a : option 'I_n) (b : option 'I_n) :=
    match a, b with
    | _, None => True
    | None, _ => False
    | Some a', Some b' => a' < b'
  end.

  Lemma rpivotlt_trans :
    forall {n} (a b c : option 'I_n),
      rpivotlt a b -> rpivotlt b c -> rpivotlt a c.
  Proof.
    intros; destruct a as [a'|]; 
    destruct b as [b'|]; destruct c as [c'|];
    simpl rpivotlt in *; lia.
  Qed.

  (** 判断行阶梯行， 对于矩阵M, 右下角 x * y 的子矩阵为行阶梯行 *)
  Definition isREF {r c} (M : mat (S r) (S c)) (x y : nat) : Prop :=
    forall i j :'I_(S r), S r - x <= i -> i < j ->
      rpivotlt (getrowPivot M y i) (getrowPivot M y j).

  Lemma isREF_row0 :
    forall y {r c} (M : mat (S r) (S c)), isREF M 0 y.
  Proof.
    unfold isREF; intros. simpl in H. pose proof (fin2nat_lt i). lia.
  Qed.

  Lemma isREF_row1 : 
    forall y {r c} (M : mat (S r) (S c)), isREF M 1 y.
  Proof.
    unfold isREF; intros. simpl in H. rewrite Nat.sub_0_r in H.
    assert (r < j) by lia. pose proof (fin2nat_lt j). lia.
  Qed.

  Lemma isREF_col0 :
    forall x {r c} (M : mat (S r) (S c)), isREF M x 0.
  Proof.
    unfold isREF; intros. simpl. auto.
  Qed.

  Lemma isREF_row_intro :
    forall {r c} (M : mat (S r) (S c)) (x y : nat),
      isREF M x y ->
      rpivotlt (getrowPivot M y #(r - x)) (getrowPivot M y #(S r - x)) ->
      isREF M (S x) y.
  Proof.
    unfold isREF; intros. simpl in H1. destruct (i??=r-x).
    - assert (x <> O). { 
        intro; subst. assert (r<j) by fin. pose proof (fin2nat_lt j). lia. }
      replace (getrowPivot M y i) with (getrowPivot M y #(r - x)).
      2: { f_equal. apply fin2nat_eq_iff; fin. } destruct (j??=S r - x).
      + replace (getrowPivot M y j) with (getrowPivot M y #(S r - x)). auto.
        f_equal. apply fin2nat_eq_iff; fin.
      + eapply rpivotlt_trans. apply H0. apply H; fin.
    - apply H; fin.
  Qed. 

  Lemma isREF_col_intro :
    forall {r c} (M : mat (S r) (S c)) (x y : nat),
      isREF M x y ->
      getcolPivot M x #(c - y) = None -> 
      isREF M x (S y).
  Proof.
      unfold isREF; intros. specialize H with i j.
      replace (getrowPivot M (S y) i) with (getrowPivot M y i).
      replace (getrowPivot M (S y) j) with (getrowPivot M y j).
      apply H; try easy.
      symmetry; apply getcolPivotNone_getrowPivot with (i:=j) in H0; 
      try easy; try lia.
      symmetry; apply getcolPivotNone_getrowPivot with (i:=i) in H0; 
      try easy.
  Qed.

  Lemma isREF_row_inv :
    forall {r c} (M : mat (S r) (S c)) (x y : nat),
      isREF M (S x) y -> isREF M x y.
  Proof.
    unfold isREF; intros. apply H; try easy; lia.
  Qed.

  Lemma isREF_intro :
    forall {r c} (M : mat (S r) (S c)) (x y : nat),
    isREF M x y ->
    M.[#(r - x)].[#(c - y)] <> 0 ->
    getcolPivot M x #(c - y) = None ->
    isREF M (S x) (S y).
  Proof.
    intros. destruct (x ??= O) as [E|E]. subst. apply isREF_row1.
    apply isREF_col_intro in H; try easy.
    apply isREF_row_intro; auto.
    replace (getrowPivot M (S y) #(r - x)) with (Some (#(c - y) : fin (S c))).
    2: { symmetry. simpl. destruct (Aeqdec (M #(r - x) #(c - y)) 0) as [E0|E0]; easy. }
    destruct (getrowPivot M (S y) #(S r - x)) as [a|] eqn : E1; try easy. simpl.
    apply nat_le_neq_imply_lt. apply getrowPivot_min in E1. 
    replace (S c - S y) with (c - y) in E1 by lia. 
    rewrite fin2nat_nat2finS; try easy; try lia. 
    intro. apply getrowPivot_imply_nonzero in E1.
    apply E1. rewrite getcolPivot_None in H1. rewrite fin2nat_eq_iff in H2.
    rewrite <- H2. apply H1. fin.
  Qed.

  Lemma isREF_row_Some : 
    forall x y {r c} (M : mat (S r) (S c)) (i : 'I_(S r)) (a : 'I_(S c)),
    (S r - x) <= i -> getrowPivot M y i = Some a ->
    isREF M x y -> (forall (i': 'I_(S r)) (j': 'I_(S c)), i < i' -> S c - y <= j' ->  j' <= a -> M.[i'].[j'] = 0).
  Proof.
    intros. apply NNPP. intro. 
    apply getrowPivot_neqzero with (y:=y) in H5; auto.
    destruct H5 as [b [H5 H6]]. assert (b <= a) by lia.
    unfold isREF in H1. specialize H1 with (i:=i) (j:=i').
    apply H1 in H; fin. rewrite H0 in H. rewrite H5 in H.
    simpl in H. lia.
  Qed.

  Lemma isREF_row_None : 
    forall x y {r c} (M : mat (S r) (S c)) (i : 'I_(S r)),
    (S r - x) <= i -> getrowPivot M y i = None ->
    isREF M x y -> (forall (i': 'I_(S r)) (j': 'I_(S c)), i < i' -> S c - y <= j' ->  M.[i'].[j'] = 0).
  Proof.
    intros. apply NNPP. intro. 
    apply getrowPivot_neqzero with (y:=y) in H4; auto.
    destruct H4 as [b [H4 H5]].
    unfold isREF in H1. specialize H1 with (i:=i) (j:=i').
    apply H1 in H; fin. rewrite H0 in H. rewrite H4 in H.
    simpl in H. lia.
  Qed. 

  Lemma mrowAdd_keep_isREF : 
  forall (x y : nat) {r c} (M : mat (S r) (S c)) (i i' : 'I_(S r)) (k : tA),
    x <= S r ->  i' < i -> 
    isREF M x y ->
    isREF (mrowAdd i' i k M) x y.
  Proof.
    induction x; intros. 1:{ apply isREF_row0. }
    destruct (x ??= 0)%nat as [E|E]. 1:{ subst. apply isREF_row1. }
    apply isREF_row_intro. 
    - replace (S r - S x) with (r - x) in H by lia.
      destruct (i' ??= r - x) as [E'|E']. 
      + unfold isREF. unfold isREF in H1. intros a b. intros.
        assert (i' < a) by lia. assert (i' < b) by lia.
        replace (getrowPivot (mrowAdd i' i k M) y a) with 
          (getrowPivot M y a).
        replace (getrowPivot (mrowAdd i' i k M) y b) with
          (getrowPivot M y b). apply H1; fin. 
        * apply getrowPivot_same_row. unfold mrowAdd.
          extensionality j'. destruct (b ??= i') as [E1|E1]; try lia; auto.
        * apply getrowPivot_same_row. unfold mrowAdd.
          extensionality j'. destruct (a ??= i') as [E1|E1]; try lia; auto.
      + apply IHx; fin. apply isREF_row_inv; auto.
    - replace (getrowPivot (mrowAdd i' i k M) y #(r - x)) with
        (getrowPivot M y #(r - x)).
      replace (getrowPivot (mrowAdd i' i k M) y #(S r - x)) with
        (getrowPivot M y #(S r - x)).
      assert (x <= r) by lia. clear H. unfold isREF in H1. apply H1; fin.
      + destruct (i' ??= S r - x ) as [E'|E'].
        2:{ apply getrowPivot_same_row.  unfold mrowAdd.
            extensionality j. destruct (#(S r - x) ??= i') as [E0|E0]; auto.
            rewrite fin2nat_nat2finS in E0; lia. }
        pose proof (getrowPivot_dec y M #(S r - x)). destruct H2 as [[a H2] | H2].
        * rewrite H2; symmetry. assert (H3:=H2). rewrite getrowPivot_eq_Some in H2.
          destruct H2 as [H2 [H4 H5]]. apply getrowPivot_eq_Some.
          repeat split; fin; unfold mrowAdd.
          ** destruct (#(S r - x) ??= i') as [E0|E0]; auto.
             replace (M i a) with 0. replace (M #(S r - x) a + k * 0)%A with (M #(S r - x) a) by fin.
             auto. symmetry. pose proof (isREF_row_Some (S x) y M #(S r - x) a).
             apply H6; fin.
          ** destruct (#(S r - x) ??= i') as [E0|E0]; auto.
             replace (M i j) with 0. replace (M #(S r - x) j + k * 0)%A with (M #(S r - x) j) by fin.
             apply getrowPivot_eq_Some in H3. destruct H3 as [H3 [H8 H9]]. apply H9; fin.
             symmetry. pose proof (isREF_row_Some (S x) y M #(S r - x) a).
             specialize H8 with (i':=i) (j':=j). apply H8; fin.
        * rewrite H2. symmetry. apply getrowPivot_eq_None; intros. assert (H4:=H2).
         rewrite getrowPivot_eq_None in H2.
          unfold mrowAdd. destruct (#(S r - x) ??= i') as [E0|E0]; auto. replace (M i j) with 0.
          replace (M #(S r - x) j + k * 0)%A with (M #(S r - x) j) by fin.
          apply H2; fin. symmetry. pose proof (isREF_row_None (S x) y M #(S r - x)).
          specialize H5 with (i':=i) (j':=j). apply H5; fin.
       + destruct (i' ??= r - x ) as [E'|E'].
        2:{ apply getrowPivot_same_row.  unfold mrowAdd.
            extensionality j. destruct (#(r - x) ??= i') as [E0|E0]; auto.
            rewrite fin2nat_nat2finS in E0; lia. }
        pose proof (getrowPivot_dec y M #(r - x)). destruct H2 as [[a H2] | H2].
        * rewrite H2; symmetry. assert (H3:=H2). rewrite getrowPivot_eq_Some in H2.
          destruct H2 as [H2 [H4 H5]]. apply getrowPivot_eq_Some.
          repeat split; fin; unfold mrowAdd.
          ** destruct (#(r - x) ??= i') as [E0|E0]; auto.
             replace (M i a) with 0. replace (M #(r - x) a + k * 0)%A with (M #(r - x) a) by fin.
             auto. symmetry. pose proof (isREF_row_Some (S x) y M #(r - x) a).
             apply H6; fin.
          ** destruct (#(r - x) ??= i') as [E0|E0]; auto.
             replace (M i j) with 0. replace (M #(r - x) j + k * 0)%A with (M #(r - x) j) by fin.
             apply getrowPivot_eq_Some in H3. destruct H3 as [H3 [H8 H9]]. apply H9; fin.
             symmetry. pose proof (isREF_row_Some (S x) y M #(r - x) a).
             specialize H8 with (i':=i) (j':=j). apply H8; fin.
        * rewrite H2. symmetry. apply getrowPivot_eq_None; intros. assert (H4:=H2).
         rewrite getrowPivot_eq_None in H2.
          unfold mrowAdd. destruct (#(r - x) ??= i') as [E0|E0]; auto. replace (M i j) with 0.
          replace (M #(r - x) j + k * 0)%A with (M #(r - x) j) by fin.
          apply H2; fin. symmetry. pose proof (isREF_row_None (S x) y M #(r - x)).
          specialize H5 with (i':=i) (j':=j). apply H5; fin.
  Qed. 

  (** 判断首元是否为 1 *)
  Definition isRowPivotOne {r c : nat} (M: mat (S r) (S c)) x y: Prop :=
    forall (i : 'I_(S r)) (j : 'I_(S c)), 
    S r - x <= i -> getrowPivot M y i = Some j -> M.[i].[j] = 1.

  Lemma isRowPivotOne_row0 :
    forall y {r c : nat} (M: mat (S r) (S c)),
    isRowPivotOne M 0 y.
  Proof.
    unfold isRowPivotOne; intros. pose proof (fin2nat_lt i); lia.
  Qed.

  Lemma isRowPivotOne_col0 :
    forall x {r c : nat} (M: mat (S r) (S c)),
    isRowPivotOne M x 0.
  Proof.
    unfold isRowPivotOne; intros. inv H0.
  Qed.

  Lemma isRowPivotOne_row_intro_Some :
    forall x y {r c : nat} (M: mat (S r) (S c)) (j : 'I_(S c)),
    getrowPivot M y #(r - x) = Some j->
    M.[#(r - x)].[j] = 1 ->
    isRowPivotOne M x y ->
    isRowPivotOne M (S x) y.
  Proof.
    unfold isRowPivotOne; intros. rename j0 into a.
    replace (S r - S x) with (r - x) in H2 by lia.
    destruct (i ??= r - x) as [E | E].
    - replace i with (#(r - x) : 'I_(S r)) in *.
      2: { apply fin2nat_eq_iff; rewrite fin2nat_nat2finS; lia. }
      rewrite H in H3; inv H3. auto.
    - apply H1; fin.
  Qed.

  Lemma isRowPivotOne_row_intro_None:
    forall x y {r c : nat} (M: mat (S r) (S c)),
    getrowPivot M y #(r - x) = None ->
    isRowPivotOne M x y ->
    isRowPivotOne M (S x) y.
  Proof.
    unfold isRowPivotOne; intros.
    replace (S r - S x) with (r - x) in H1 by lia.
    destruct (i ??= r - x) as [E | E].
    - replace i with (#(r - x) : 'I_(S r)) in *.
      2: { apply fin2nat_eq_iff; rewrite fin2nat_nat2finS; lia. }
      rewrite H in H2. inv H2.
    - apply H0; fin.
  Qed.
  
  Lemma isRowPivotOne_col_intro :
    forall x y {r c : nat} (M: mat (S r) (S c)),
    getcolPivot M x #(c - y) = None ->
    isRowPivotOne M x y ->
    isRowPivotOne M x (S y).
  Proof.
    unfold isRowPivotOne; intros.
    replace (getrowPivot M (S y) i) with (getrowPivot M y i) in H2.
    2 :{ symmetry; apply getcolPivotNone_getrowPivot with (x := x); fin. }
    apply H0; fin.
  Qed.
  
  Lemma isRowPivotOne_intro :
    forall x y {r c : nat} (M: mat (S r) (S c)) (j : 'I_(S c)),
    getcolPivot M x #(c - y) = None ->
    getrowPivot M (S y) #(r - x) = Some j->
    M.[#(r - x)].[j] = 1 ->
    isRowPivotOne M x y ->
    isRowPivotOne M (S x) (S y).
  Proof.
    intros. apply isRowPivotOne_row_intro_Some with (j:=j); auto.
    apply isRowPivotOne_col_intro; auto.
  Qed.
  
  Lemma isRowPivotOne_row_inv :
    forall {r c} (M : mat (S r) (S c)) (x y : nat),
    isRowPivotOne M (S x) y -> isRowPivotOne M x y.
  Proof.
    unfold isRowPivotOne; intros. apply H; try easy; lia.
  Qed.

  Lemma mrowAdd_keep_isRowPivotOne : 
  forall (x y : nat) {r c} (M : mat (S r) (S c)) (i i' : 'I_(S r)) (k : tA),
    x <= S r ->  i' < i -> 
    isREF M x y -> isRowPivotOne M x y ->
    isRowPivotOne (mrowAdd i' i k M) x y.
  Proof.
    induction x; intros. 1:{ apply isRowPivotOne_row0. }
    pose proof (getrowPivot_dec y M #(r - x)). destruct H3 as [[a E]|E].
    - assert (H3 := E). rewrite getrowPivot_eq_Some in H3.  destruct H3 as [H3 [H4 H5]].
      apply isRowPivotOne_row_intro_Some with (j:=a).
      + rewrite getrowPivot_eq_Some. repeat split; fin; unfold mrowAdd.
        * destruct (#(r - x) ??= i') as[E'|E']; auto. replace (M i a) with 0.
          replace (M #(r - x) a + k * 0)%A with (M #(r - x) a)%A by fin; auto.
          symmetry. pose proof (isREF_row_Some (S x) y M #(r - x) a).
          specialize H6 with (i':=i) (j':=a). apply H6; fin.
        * destruct (#(r - x) ??= i') as[E'|E']. 2: { apply H5; fin. } replace (M i j) with 0.
          replace (M #(r - x) j + k * 0)%A with (M #(r - x) j)%A by fin; auto.
          symmetry.  pose proof (isREF_row_Some (S x) y M #(r - x) a).
          specialize H8 with (i':=i) (j':=j). apply H8; fin.
      + unfold mrowAdd. destruct (#(r - x) ??= i') as [E'|E'].
        * replace (M i a) with 0. replace (M #(r - x) a + k * 0)%A with (M #(r - x) a) by fin.
          unfold isRowPivotOne in H2; apply H2 in E; fin. symmetry.
          pose proof (isREF_row_Some (S x) y M #(r - x) a).
          specialize H6 with (i':=i) (j':=a). apply H6; fin.
        * unfold isRowPivotOne in H2; apply H2 in E; fin.
      + apply IHx; fin. apply isREF_row_inv; auto. apply isRowPivotOne_row_inv; auto.
    - assert (H3:=E). rewrite getrowPivot_eq_None in H3. apply isRowPivotOne_row_intro_None.
      + rewrite getrowPivot_eq_None; intros. unfold mrowAdd.
        destruct (#(r - x) ??= i') as [E'|E']. 2: { apply H3; fin. }
        replace (M i j) with 0. replace (M #(r - x) j + k * 0)%A with (M #(r - x) j)%A by fin.
        apply H3; fin. symmetry. pose proof (isREF_row_None (S x) y M #(r - x)).
        specialize H5 with (i':=i) (j':=j). apply H5; fin.
      + apply IHx; fin. apply isREF_row_inv; auto. apply isRowPivotOne_row_inv; auto.
  Qed. 

  (** 行首元也会是列首元 *)
  Definition isbothPivot {r c} (M : mat (S r) (S c)) (x : nat) :=
    forall (i : 'I_(S r)) (j : 'I_(S c)), i < x ->
    getrowPivot M (S c) i = Some j -> getcolPivot M (S r) j = Some i.

  Lemma isbothPivot_row0 :
    forall {r c} (M : mat (S r) (S c)), isbothPivot M 0.
  Proof.
    unfold isbothPivot; intros. inv H.
  Qed.

  Lemma isbothPivot_intro :
    forall x {r c} (M : mat (S r) (S c)),
    (forall j : 'I_(S c), getrowPivot M (S c) #x = Some j -> getcolPivot M (S r) j = Some #x) ->
    isbothPivot M x -> isbothPivot M (S x).
  Proof.
    unfold isbothPivot; intros. destruct (i ??= x) as [E|E].
    - assert (x < S r). { pose proof (fin2nat_lt i). lia. }
      replace i with (#x : 'I_(S r)) in *.
      2:{  apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; lia. }
      apply H; fin.
    - apply H0; fin.
  Qed. 

  Lemma isbothPivot_row_inv :
    forall {r c} (M : mat (S r) (S c)) (x : nat),
      isbothPivot M (S x) -> isbothPivot M x.
  Proof.
    unfold isbothPivot; intros. apply H; try easy; lia.
  Qed.

  Lemma mrowAdd_keep_isbothPivot : 
  forall (n : nat) {r c} (M : mat (S r) (S c)) (i i' : 'I_(S r)) (k : tA),
    i' < i -> n <= i ->
    isREF M (S r) (S c) -> isbothPivot M n ->
    isbothPivot (mrowAdd i' i k M) n.
  Proof.
    induction n; intros. 1:{ apply isbothPivot_row0. }
    assert (n < r). { pose proof (fin2nat_lt i). lia. } apply isbothPivot_intro; intros.
    - clear IHn. unfold isbothPivot in H2.
      specialize H2 with (i:=#n) (j:=j).
      pose proof (getrowPivot_dec (S c) M #n). destruct H5 as [[a H5] | H5].
      + assert (getrowPivot (mrowAdd i' i k M) (S c) #n = Some a).
        * assert (H6 := H5).
          rewrite getrowPivot_eq_Some in H6. destruct H6 as [_ [H6 H7]].
          rewrite getrowPivot_eq_Some. repeat split; fin; unfold mrowAdd.
          ** destruct (#n ??= i') as [E'|E']; fin. replace (M i a)%A with 0.
             replace (M #n a + k * 0)%A with (M #n a)%A by fin; auto.
             symmetry. pose proof (isREF_row_Some (S r) (S c) M #n a).
             specialize H8 with (i':=i) (j':=a). apply H8 in H5; fin.
          ** rename j0 into b. replace (M i b) with 0. replace (M #n b) with 0.
            destruct (#n ??= i'); fin.
            *** symmetry. apply H7; fin.
            *** symmetry. pose proof (isREF_row_Some (S r) (S c) M #n a).
                specialize H10 with (i':=i) (j':=b). apply H10 in H5; fin.
        * rewrite H4 in H6. inv H6. apply H2 in H5 as H6; fin. rewrite <- H6.
          apply getcolPivot_same_col. extensionality b. unfold mcol, mrowAdd.
          destruct (b ??= i') as [E|E]; auto. replace (M i a) with 0. fin.
          symmetry. pose proof (isREF_row_Some (S r) (S c) M #n a).
          specialize H7 with (i':=i) (j':=a). apply H7 in H5; fin.
      + assert (getrowPivot (mrowAdd i' i k M) (S c) #n = None).
        * assert (H6 := H5).
          rewrite getrowPivot_eq_None in H6.
          rewrite getrowPivot_eq_None. intros b; unfold mrowAdd; intros.
          destruct (#n ??= i') as [E'|E']; fin. replace (M i b)%A with 0.
          replace (M #n b) with 0. fin.
            ** symmetry. apply H6; fin.
            ** symmetry. pose proof (isREF_row_None (S r) (S c) M #n).
               specialize H8 with (i':=i)(j':=b). apply H8; fin.
        * rewrite H4 in H6; inv H6.
    - apply IHn; fin. apply isbothPivot_row_inv. auto.
  Qed. 

  (** 判断是否满足行最简单行 *)
  Definition isRREF {r c} (M : mat (S r) (S c)) :=
    isREF M (S r) (S c) /\ isRowPivotOne M (S r) (S c) /\ isbothPivot M (S r).


  Lemma isRREF_col_veye :
    forall {r c} (M : mat (S r) (S c)) i a,
    isRREF M -> getrowPivot M (S c) i = Some a -> M&[a] = veye #i.
  Proof.
    intros. destruct H as [H [H1 H2]]. extensionality b.
    destruct (b ??< i); [|destruct (i ??< b)]; unfold mcol, veye.
    - destruct (#i ??= b); fin. unfold isbothPivot in H2. apply H2 in H0; fin.
      rewrite getcolPivot_eq_Some in H0. destruct H0 as [H0 [H3 H4]]. apply H4; fin.
    - destruct (#i ??= b); fin. pose proof (isREF_row_Some (S r) (S c) M i a).
      specialize H3 with (i':=b) (j':=a). apply H3; fin.
    - assert (fin2nat b = fin2nat i) by lia. apply fin2nat_eq_iff in H3; subst.
      destruct (#i ??= i); fin. unfold isRowPivotOne in H1. apply H1; fin.
  Qed.
  
  (* ******************************************************************* *)
  (** ** 运算中会用到的矩阵列操作 *)

  (** 获取列主元并将其放在相应位置并置1 *)
  Definition setPivotAone {r c} (M : mat (S r) (S c)) (x y : nat) (a : 'I_(S r))
    : list RowOp * mat (S r) (S c) :=
  let i : 'I_(S r) := #(S r - x) in
  let (op1, M1) :=
  (if a ??= i     (* 若当前行就是主元行，则不需要交换 *)
    then (ROnop, M)
    else (ROswap a i, mrowSwap a i M)) in
            (* 使主元是 1 *)
  let (op2, M2) :=
    (let val : tA := M1.[i].[#(S c - y)] in
        (ROscale i (/val), mrowScale i (/val) M1)) in
  ([op2; op1]%list, M2).

  Lemma setPivotAone_keep_former_row :
    forall (x y : nat) {r c} (M M': mat (S r) (S c))  (a : 'I_(S r)) (l: list RowOp),
      O < x -> x <= r -> getcolPivot M x #(S c - y) = Some a ->
      setPivotAone M x y a = (l, M') -> 
        (forall (i : 'I_(S r)) j, i <= (r - x) -> M' i j = M i j).
  Proof.
    intros. unfold setPivotAone in H2.
    destruct (a ??= #(S r - x)); apply pair_equal_spec in H2; 
    destruct H2; rewrite <- H4.
    - unfold mrowScale; fin.
    - apply getcolPivot_min in H1. unfold mrowScale, mrowSwap. fin.
  Qed.
  
  Lemma  setPivotAone_infer_getcolPivotNone :
    forall x y n {r c} (M M': mat (S r) (S c)) (l : list RowOp) a j,
      0 < x -> x <= n ->
      getcolPivot M n j = None ->
      getcolPivot M x #(S c - y) = Some a -> 
      setPivotAone M x y a = (l, M') ->
      getcolPivot M' n j = None.
  Proof.
    intros. unfold setPivotAone in H3.
    destruct (a ??= #(S r - x)); apply pair_equal_spec in H3; destruct H3; 
    rewrite <- H4; rewrite getcolPivot_None; rewrite getcolPivot_None in H1; intros.
    - unfold mrowScale. destruct ( i ??= #(S r - x)) as [E|E].
      + assert (M i j = 0) by auto. rewrite H6. apply ring_mul_0_r.
      + auto.
    - rename n0 into E. apply getcolPivot_min in H2.
      assert (S r - x < a). { 
        replace (fin2nat (#(S r - x) : 'I_(S r))) with (S r - x) in E by fin. lia. }
      unfold mrowScale, mrowSwap. destruct (i ??= #(S r - x)).
      * destruct (#(S r - x) ??= a); fin. assert (M a j = 0). apply H1. lia.
        rewrite H7; apply ring_mul_0_r.
      * destruct (i ??= a). subst. apply H1. fin. apply H1; fin.
  Qed.
  
  Lemma setPivotAone_prop :
    forall (x y : nat) {r c} (M M': mat (S r) (S c))  (a : 'I_(S r)) (l: list RowOp),
        x <> O -> getcolPivot M x #(S c - y) = Some a ->
        setPivotAone M x y a = (l, M') -> 
          M'.[#(S r - x)].[#(S c - y)] = 1.
  Proof.
    unfold setPivotAone; intros. destruct (a ??= #(S r - x)) as [E|E];
    rewrite pair_equal_spec in H1; destruct H1 as [_ H2];
    rewrite <- H2; unfold mrowScale; rewrite fin2nat_nat2finS; try lia;
    destruct (S r - x ??= S r - x) as [E0|E0]; try lia; apply field_mulInvL.
    - rewrite fin2nat_eq_iff in E.
      rewrite E in H0. apply getcolPivot_imply_nonzero in H0. auto.
    - unfold mrowSwap. rewrite fin2nat_nat2finS in *; try lia.
      destruct (S r - x ??= a); try lia. destruct (S r - x ??= S r - x); try lia.
      apply getcolPivot_imply_nonzero in H0. auto.
  Qed.

  Lemma setPivotAone_eq :
    forall (x y : nat) {r c} (M M': mat (S r) (S c))  (a : 'I_(S r)) (l: list RowOp),
      setPivotAone M x y a = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    intros; unfold setPivotAone in H. destruct (a ??= #(S r - x));
    apply pair_equal_spec in H; destruct H; rewrite <- H0;
    rewrite <- H; rewrite rowOps2mat_cons; rewrite mmul_assoc.
    - simpl rowOps2mat at 2. rewrite mmul_1_l. simpl.
      rewrite <- mrowScale_mat1. auto.
    - assert (rowOps2mat [ROswap a #(S r - x)] * M =  mrowSwap a #(S r - x) M).
      { simpl. rewrite <- mrowSwap_mat1. auto. } rewrite H1.
      simpl. rewrite <- mrowScale_mat1. auto.
  Qed.

  Lemma setPivotAone_rowOpValid :
    forall (x y : nat) {r c} (M M': mat (S r) (S c))  (a : 'I_(S r)) (l: list RowOp),
      getcolPivot M x #(S c - y) = Some a -> setPivotAone M x y a = (l, M') -> Forall roValid l.
  Proof.
    intros; unfold setPivotAone in H0. destruct (a ??= #(S r - x)) as [E|E];
    apply pair_equal_spec in H0; destruct H0; rewrite <- H0.
    - apply fin2nat_eq_iff in E. rewrite E in H.
      apply getcolPivot_imply_nonzero in H. apply Forall_cons.
      + simpl in H. simpl. apply field_inv_neq0_if_neq0. auto.
      + apply Forall_cons; simpl; auto.
    -  apply Forall_cons.
      + assert (mrowSwap a #(S r - x) M #(S r - x) #(S c - y) <> 0 ).
        { unfold mrowSwap. destruct (#(S r - x) ??= a) as [E1|E1].
          rewrite <- E1 in E. exfalso; apply E; auto. clear E1.
          destruct (#(S r - x) ??= #(S r - x)) as [E1|E1].
          apply getcolPivot_imply_nonzero in H. auto.
          exfalso; apply E1; auto. }
        simpl in H2; simpl. apply field_inv_neq0_if_neq0. auto.
      + apply Forall_cons; simpl; auto.
  Qed.

  (** 向下消元 *)
  Fixpoint ElimDown {r c} (M : mat (S r) (S c)) (x : nat) (i: 'I_(S r)) (j : 'I_(S c))
    : list RowOp * mat (S r) (S c) :=
    match x with
    | O => ([], M)
    | S x' =>
        (* 递归时 x 从大到小，而 fx 是从小到大 *)
        let fx : 'I_(S r) := #(S r - x) in
        let a : tA := M.[fx].[j] in
        (* 如果 M[S n-x,j] <> 0，则 j 行的 -M[S n-x,j] 倍加到 S n-x 行。要求 M[j,j]=1 *)
        if Aeqdec a 0
        then ElimDown M x' i j
        else
          let op1 := ROadd fx i (-a)%A in
          let M1 := mrowAdd fx i (-a)%A M in
          let (l2, M2) := ElimDown M1 x' i j in
          ((l2 ++ [op1])%list, M2)
    end.

  Lemma ElimDown_keep_former_row :
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimDown M x i j = (l, M') ->
      x < S r - i ->
      (forall (a : 'I_(S r)) (b : 'I_(S c)), a < S r - x -> M' a b = M a b).
  Proof.
    induction x; intros.
    - simpl in H. inv H. auto.
    - simpl in H.
      destruct Aeqdec as [E|E].
      + apply IHx with (a:=a)(b:=b) in H; auto; try lia.
      + destruct ElimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H4. apply IHx with (a:=a)(b:=b) in T2; try lia.
        * rewrite T2. unfold mrowAdd; fin.
  Qed.

  Lemma ElimDown_prop:
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimDown M x i j = (l, M') ->
      M i j = 1 ->
      x < S r - i ->
      (forall a : 'I_(S r), S r - x <= a -> M' a j = 0).
  Proof.
    induction x; intros.
    - pose proof (fin2nat_lt a). lia.
    - simpl in H.
      destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + destruct (a ??= r - x) as [E1|E1].
        * apply ElimDown_keep_former_row with (a:=a)(b:=j) in H; auto; try lia.
          subst. rewrite H. rewrite <- E1 in E. rewrite nat2finS_fin2nat in E; auto.
        * apply IHx with (a:=a) in H; auto; try lia.
      + destruct ElimDown as [l2 M2] eqn: T2.
        inversion H. rewrite <- H5.
        replace (S r - S x) with (r - x) in H2 by lia.
        destruct (a ??= r - x) as [E1|E1].
        * apply ElimDown_keep_former_row with (a:=a)(b:=j) in T2; auto; try lia.
          rewrite T2. unfold mrowAdd; fin. rewrite H0. rewrite <- E0. fin.
        * apply IHx with (a:=a) in T2; auto; try lia. unfold mrowAdd; fin.
  Qed.
  
  Lemma ElimDown_infer_getcolPivot:
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimDown M x i j = (l, M') ->
      M i j = 1 ->
      x < S r - i ->
      getcolPivot M' x j = None.
  Proof.
    intros. apply getcolPivot_None. intros a; intros.
    pose proof (ElimDown_prop x M M' i j l). specialize H3 with a.
    apply H3; try easy.
  Qed.

  Lemma ElimDown_keep_getcolPivot :
    forall x n {r c} (M M': mat (S r) (S c)) (l : list RowOp) (i : 'I_(S r)) j m,
      getcolPivot M n m = None -> S r - n <= i ->
      ElimDown M x i j = (l, M') -> getcolPivot M' n m = None.
  Proof.
    induction x; intros.
    - simpl in H1; inv H1; auto.
    - simpl in H1. destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + specialize IHx with (n:=n) (M:=M) (M':=M') 
          (l:=l) (i:=i) (j:=j) (m:=m). apply IHx; fin.
      + destruct ElimDown as [l2 M2] eqn : E0. injection H1; clear H1; intros.
        specialize IHx with (n:=n) (M:=mrowAdd #(r - x) i (- M #(r - x) j) M)
          (M':=M2) (l:=l2) (i:=i) (j:=j) (m:=m).
        apply IHx in E0; fin; subst; auto.
        rewrite getcolPivot_None. intros a H1. rewrite getcolPivot_None in H.
        unfold mrowAdd. destruct (a ??= #(r - x)).
        * assert (M a m = 0) by auto. assert (M i m = 0) by auto.
          rewrite H2. rewrite H3. fin.
        * auto.
  Qed. 

  Lemma isREF_ElimDown :
    forall {r c} (M M': mat (S r) (S c)) (x y : nat) (l : list RowOp ),
      M.[#(r - x)].[#(c - y)] = 1 ->
      x <= r ->
      ElimDown M x #(r - x) #(c - y) = (l, M') ->
      isREF M' x y ->
      isREF M' (S x) (S y).
  Proof.
    intros. apply isREF_intro; try easy.
    assert (M' #(r - x) #(c - y) = M.[#(r - x)].[#(c - y)]).
    { apply ElimDown_keep_former_row with (a:=#(r - x)) (b:=#(c - y)) in H1; try easy;
      rewrite fin2nat_nat2finS; try lia. } pose proof field_1_neq_0. intro. 
    rewrite <- H in H4; rewrite <- H5 in H4. apply H4; easy.
    apply ElimDown_infer_getcolPivot in H1; auto. rewrite fin2nat_nat2finS; try lia.
  Qed. 

  Lemma ElimDown_eq :
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimDown M x i j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct ElimDown as [l2 M2] eqn: T2.
        apply IHx in T2. inversion H. rewrite <- H2, <- T2.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.

  (** 对 M 向下消元得到 (l, M')，则 l 都是有效的 *)
  Lemma ElimDown_rowOpValid :
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      x < S r - i -> ElimDown M x i j = (l, M') -> Forall roValid l.
  Proof.
    induction x; intros; simpl in *.
    - inversion H0. constructor.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #(r - x) j) 0) as [E|E].
      + apply IHx in H0; auto. lia.
      + destruct ElimDown as [l2 M2] eqn: T2.
        apply IHx in T2; try lia. inversion H0.
        apply Forall_app. split; auto. repeat constructor. hnf. intro.
        destruct j.
        assert (r - x = i). {apply fin2nat_eq_iff in H1. fin. }
        fin. subst. destruct (r - x) eqn:H2. fin. fin.
  Qed.

  (** ** 向上消元 *)
  Fixpoint ElimUp {r c} (M : mat (S r) (S c)) (x : nat) (i: 'I_(S r)) (j : 'I_(S c))
    : list RowOp * mat (S r) (S c) :=
    match x with
    | O => ([], M)
    | S x' =>
        (* 递归时 x 从大到小，而 fx 是从小到大 *)
        let fx : 'I_(S r) := # x' in
        let a : tA := M.[fx].[j] in
        (* 如果 M[x',j] <> 0，则 j 行的 -M[i,j] 倍加到 x'行。要求 M[j,j]=1 *)
        if Aeqdec a 0
        then ElimUp M x' i j
        else
          let op1 := ROadd fx i (-a)%A in
          let M1 := mrowAdd fx i (-a)%A M in
          let (l2, M2) := ElimUp M1 x' i j in
          ((l2 ++ [op1])%list, M2)
    end.

  Lemma ElimUp_keep_former_row :
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimUp M x i j = (l, M') ->
      M i j = 1 ->
      x <= i ->
      (forall (a : 'I_(S r)) , x <= a -> M' a = M a).
  Proof.
    induction x; intros.
    - simpl in H; inversion H; subst; auto.
    - simpl in H.
      destruct Aeqdec as [E|E].
      + destruct (x ??= i) as [E'|E']. rewrite E' in E. 
        rewrite nat2finS_fin2nat in E. rewrite E in H0. exfalso.
        apply field_1_neq_0. symmetry; auto.
        assert (x <= i) by fin.
        apply IHx with (a:=a) in H; auto; lia.
      + destruct ElimUp as [l2 M2] eqn: T2.
        inversion H. subst. apply IHx with (a:=a) in T2; try lia.
        * rewrite T2. unfold mrowAdd; fin. pose proof (fin2nat_lt i). lia.
        * unfold mrowAdd; fin. pose proof (fin2nat_lt i). lia.
  Qed.

  Lemma ElimUp_prop:
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimUp M x i j = (l, M') ->
      M i j = 1 ->
      x <= i ->
      (forall a : 'I_(S r), a < x -> M' a j = 0).
  Proof.
    induction x; intros.
    - inv H2.
    - simpl in H.
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + destruct (x ??= i) as [E'|E']. rewrite E' in E.
        rewrite nat2finS_fin2nat in E. rewrite E in H0. exfalso.
        apply field_1_neq_0. symmetry; auto.
        assert (x <= i) by fin. clear H1; clear E'.
        destruct (a ??= x) as [E0 | E0].
        * pose proof (ElimUp_keep_former_row x M M' i j l).
          specialize H1 with (a := a). apply H1 in H; subst; auto.
          rewrite H. rewrite <- E; f_equal; fin.
        * assert (a < x) by fin. clear H2; clear E0. specialize IHx with (a:=a).
          apply IHx in H; auto.
      + destruct ElimUp as [l2 M2] eqn: T2. inversion H. subst M2.
        clear H. destruct (a ??= x) as [E'|E'].
        * pose proof (ElimUp_keep_former_row a (mrowAdd #a i (- M #a j) M) M' i j l2).
          specialize H with (a := a). subst x. apply H in T2; clear H; fin.
          rewrite T2. unfold mrowAdd. destruct (a ??= a); fin. rewrite H0. fin.
          unfold mrowAdd. destruct (a ??= a); fin.
        * specialize IHx with (a:=a). apply IHx in T2; fin. unfold mrowAdd.
          destruct (i ??= #x); fin. pose proof (fin2nat_lt i). lia.
  Qed.

  Lemma ElimUp_infer_getcolPivot:
    forall {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimUp M i i j = (l, M') ->
      M i j = 1 ->
      getcolPivot M' (S r) j = Some i.
  Proof.
    intros. apply getcolPivot_Some. split; [| split]; auto; try lia.
    - pose proof (ElimUp_keep_former_row i M M' i j l).
      specialize H1 with (a:=i). apply H1 in H; fin.
      rewrite H. rewrite H0. apply field_1_neq_0.
    - intros a; intros. pose proof (ElimUp_prop i M M' i j l).
      specialize H3 with (a:=a). apply H3 in H; fin.
  Qed.

  Lemma ElimUp_keep_isREF :
    forall x {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (a : 'I_(S c)) (l : list RowOp),
      x <= i -> 
      getrowPivot M (S c) i = Some a ->
      M.[i].[a] = 1 ->
      isREF M (S r) (S c) ->
      ElimUp M x i a = (l, M') ->
      isREF M' (S r) (S c).
  Proof.
    induction x; intros.
    - simpl in H3. inv H3; auto.
    - simpl in H3. destruct (Aeqdec (M #x a) 0) as [E|E].
      + apply IHx in H3; fin.
      + destruct ElimUp as [l2 M2] eqn : E1 in H3. injection H3; intros. subst M2.
        assert (x < S r). { pose proof (fin2nat_lt i). lia. } apply IHx in E1; fin.
        * rewrite getrowPivot_eq_Some. rewrite getrowPivot_eq_Some in H0.
          destruct H0 as [_ [H0 H6]]. repeat split; try lia.
          ** unfold mrowAdd. destruct (i ??= #x) as [E2|E2]; fin.
          ** intros. unfold mrowAdd. destruct (i ??= #x) as [E2|E2]; fin.
        * unfold mrowAdd. destruct (i ??= #x) as [E2|E2]; auto.
          rewrite E2 in H. rewrite fin2nat_nat2finS in H; lia.
        * apply mrowAdd_keep_isREF; fin.
  Qed.

  Lemma ElimUp_keep_isRowPivotOne :
    forall x {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (a : 'I_(S c)) (l : list RowOp),
      x <= i -> 
      isREF M (S r) (S c) ->
      isRowPivotOne M (S r) (S c) ->
      ElimUp M x i a = (l, M') ->
      isRowPivotOne M' (S r) (S c).
  Proof.
    induction x; intros.
    - simpl in H2. inv H2; auto.
    - simpl in H2. destruct (Aeqdec (M #x a) 0) as [E|E].
      + apply IHx in H2; fin.
      + destruct ElimUp as [l2 M2] eqn : E1 in H2. injection H2; intros. subst M2.
        assert (x < S r). { pose proof (fin2nat_lt i). lia. } apply IHx in E1; fin.
        * apply mrowAdd_keep_isREF; fin.
        * apply mrowAdd_keep_isRowPivotOne; fin.
  Qed.

  Lemma ElimUp_keep_isbothPivot :
    forall x n {r c} (M M' : mat (S r) (S c)) (l : list RowOp) (i : 'I_(S r)) (a : 'I_(S c)),
      x <= i -> n <= i -> isREF M (S r) (S c) -> 
      getrowPivot M (S c) i = Some a -> ElimUp M x i a = (l, M') ->
      isbothPivot M n -> isbothPivot M' n.
  Proof.
    induction x; intros. 1:{ inv H3; auto. }
    simpl in H3. destruct (Aeqdec (M #x a) 0) as [E|E].
    - apply IHx with (n:=n) in H3; fin.
    - destruct ElimUp as [l2 M2] eqn : E'. inv H3.
      apply IHx with (n:=n) in E'; fin.
      + pose proof (mrowAdd_keep_isREF (S r) (S c) M i #x (- M #x a)).
        apply H3 in H1; auto; try lia. rewrite fin2nat_nat2finS; try lia.
        pose proof (fin2nat_lt i); lia.
      + rewrite <- H2. apply getrowPivot_same_row. unfold mrowAdd .
        extensionality j. destruct (i ??= #x) as [E0|E0]; try easy.
        rewrite fin2nat_nat2finS in E0; try lia.
        pose proof (fin2nat_lt i). lia.
  + apply mrowAdd_keep_isbothPivot; fin. pose proof (fin2nat_lt i). lia.
  Qed.
      
  (** 对 M 向下消元得到 (l, M')，则 [l] * M = M' *)
  Lemma ElimUp_eq :
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      ElimUp M x i j = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros; simpl in *.
    - inversion H. simpl. apply mmul_1_l.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + apply IHx in H; auto.
      + destruct ElimUp as [l2 M2] eqn: T2.
        apply IHx in T2. inversion H. rewrite <- H2, <- T2.
        rewrite rowOps2mat_app. simpl.
        rewrite !mmul_assoc. f_equal.
        rewrite <- mrowAdd_mmul. rewrite mmul_1_l. auto.
  Qed.

  Lemma ElimUp_rowOpValid :
    forall (x : nat) {r c} (M M' : mat (S r) (S c)) (i : 'I_(S r)) (j : 'I_(S c)) (l : list RowOp),
      x <= i -> ElimUp M x i j = (l, M') -> Forall roValid l.
  Proof.
    induction x; intros; simpl in *.
    - inversion H0. constructor.
    - (* 当前元素是否为0，若是则直接递归，若不是则消元后递归 *)
      destruct (Aeqdec (M #x j) 0) as [E|E].
      + assert (x < S r). {pose proof (fin2nat_lt i); lia. }
        destruct ((#x : 'I_(S r)) ??= i) as [E'|E']. rewrite fin2nat_nat2finS in E'; auto.
        rewrite E' in H; lia. apply IHx in H0; auto. lia.
      + destruct ElimUp as [l2 M2] eqn: T2. apply IHx in T2; try lia.
        inversion H0; subst. apply Forall_app. split; auto.
        repeat constructor. hnf. intros. assert (x < S r). {pose proof (fin2nat_lt i); lia. }
        rewrite <- H1 in H. rewrite fin2nat_nat2finS in H; try lia.
  Qed.

  (* ******************************************************************* *)
  (** ** 矩阵化简算法 *)

  (** 化简为行阶梯行 *)
  Fixpoint toREF {r c} (M : mat (S r) (S c)) (x : nat) (y : nat)
    : list RowOp * mat (S r) (S c):=
    match x, y with
    | O, _ => ([], M)
    | _, O => ([], M)
    | S x', S y' =>
        let i : 'I_(S r) := #(S r - x) in
        let j : 'I_(S c) := #(S c - y) in
        (* 找出主元 *)
        match getcolPivot M x j with
        | None => toREF M x y' (* 没有非零元，跳过该列 *)
        | Some a => 
            (* 找到主元并归一*)
            let (l1, M1) := setPivotAone M x y a in
            (* 使主元以下都是 0 *)
            let (l2, M2) := ElimDown M1 x' i j in
            (* 递归 *)
            let (l3, M3) := toREF M2 x' y' in
            ((l3 ++ l2 ++ l1)%list, M3)
        end
    end.


  Fixpoint toREF' {r c} (M : mat (S r) (S c)) (x : nat) (y : nat)
    : list RowOp * mat (S r) (S c) * nat :=
    match x, y with
    | O, _ => ([], M, O)
    | _, O => ([], M, O)
    | S x', S y' =>
        let i : 'I_(S r) := #(S r - x) in
        let j : 'I_(S c) := #(S c - y) in
        (* 找出主元 *)
        match getcolPivot M x j with
        | None => toREF' M x y'(* 没有非零元，跳过该列 *)
        | Some a => 
            (* 找到主元并归一*)
            let (l1, M1) := setPivotAone M x y a in
            (* 使主元以下都是 0 *)
            let (l2, M2) := ElimDown M1 x' i j in
            (* 递归 *)
            let '(l3, M3, num) := toREF' M2 x' y' in
            ((l3 ++ l2 ++ l1)%list, M3, S num)
        end
    end.

  Opaque getcolPivot.

  Lemma test :
    forall x y {r c} (M M': mat (S r) (S c))  (l : list RowOp) (num : nat),
      x <= r -> toREF' M x y = (l, M', num) -> num <= y.
  Proof.
    intros x y. generalize dependent x. induction y; intros.
    - simpl in H0. destruct x; inv H0; fin.
    - destruct x. simpl in H0. inv H0; lia. simpl in H0.
      destruct (getcolPivot M (S x) #(c - y)).
      + destruct (setPivotAone). destruct (ElimDown). destruct toREF' as [[l3 M3] num'] eqn : E.
        injection H0; intros. rewrite <- H1. apply IHy in E. lia. lia.
      + apply IHy in H0. lia. lia. 
  Qed.
  
  Lemma toREF_keep_former_row :
    forall x y {r c} (M M': mat (S r) (S c))  (l : list RowOp),
      x <= r -> toREF M x y = (l, M') ->
      (forall (i : 'I_(S r)) j, i <= (r - x) -> M' i j = M i j).
  Proof.
    intros x y; generalize dependent x; induction y; destruct x; intros;
    try (simpl in H0; injection H0; intros; subst; auto). simpl in H0.
    destruct (getcolPivot M (S x) #(c - y)) as [a|] eqn : E. 
    - destruct setPivotAone as [l1 M1] eqn : E1.
      destruct ElimDown as [l2 M2] eqn : E2.
      destruct (toREF M2 x y) as [l3 M3] eqn : E3.
      injection H0; clear H0; intros; subst.
      specialize IHy with (i:=i) (j:=j). apply IHy in E3; fin. rewrite E3.
      pose proof (ElimDown_keep_former_row x M1 M2 #(r - x) #(c - y) l2).
      specialize H0 with (a:=i) (b:=j). apply H0 in E2; fin.
      rewrite E2.
      pose proof (setPivotAone_keep_former_row (S x) (S y) M M1 a l1).
      specialize H2 with (i:=i) (j:=j). apply H2 in E1; fin.
    - specialize IHy with (i:=i) (j:=j). apply (IHy (S x) M M' l) in H; fin.
  Qed.

  Lemma toREF_keep_getcolPivot :
    forall x y n {r c} (M M': mat (S r) (S c))  (l : list RowOp) j,
    getcolPivot M n j = None -> x <= n -> j < (S c - y) ->
    toREF M x y = (l, M') -> getcolPivot M' n j = None.
  Proof.
    intros x y; generalize dependent x; induction y; destruct x; intros;
    try (simpl in H2; injection H2; intros; subst; auto).
    replace (S c - S y) with (c - y) in * by lia.
    simpl in H2. destruct (getcolPivot M (S x) #(c - y)) as [a|] eqn : E.
    - destruct setPivotAone as [l1 M1] eqn : E1.
      destruct ElimDown as [l2 M2] eqn : E2.
      destruct (toREF M2 x y) as [l3 M3] eqn : E3.
      injection H2; clear H2; intros; subst.
      specialize IHy with (x:=x) (n:=n) (M:=M2) (M':=M') (l:=l3) (j:=j).
      apply IHy in E3; fin.
      pose proof (ElimDown_keep_getcolPivot x n M1 M2 l2 #(r - x) #(c - y) j).
      apply H2; fin.
      pose proof (setPivotAone_infer_getcolPivotNone (S x) (S y) n M M1 l1 a j).
      apply H3; fin.
    - specialize IHy with (x:=S x) (n:=n) (M:=M) (M':=M') (l:=l) (j:=j).
      apply IHy; fin.
  Qed.
  
  Lemma toREF_isREF :
    forall x y {r c} (M M': mat (S r) (S c))  (l : list RowOp),
    x <= S r -> y <= S c -> toREF M x y = (l, M') -> isREF M' x y.
  Proof.
    intros x y. generalize dependent x. 
    induction y; intros. apply isREF_col0. destruct x.
    apply isREF_row0. simpl in H1.
    destruct (getcolPivot M (S x) #(c - y)) as [a|] eqn : E.
    - destruct setPivotAone as [l1 M1] eqn : E1.
      destruct ElimDown as [l2 M2] eqn : E2.
      destruct (toREF M2 x y) as [l3 M3] eqn : E3. 
      injection H1; clear H1; intros. subst; fin.
      pose proof (setPivotAone_prop (S x) (S y) M M1 a l1). fin.
      assert (M1.[#(S r - S x)].[#(S c - S y)] = 1) by (apply H1; try easy).
      clear H1. replace (S r - S x) with (r - x) in * by lia.
      replace (S c - S y) with (c - y) in * by lia.
      apply IHy in E3 as H3; try lia. apply isREF_intro; try easy.
      pose proof (toREF_keep_former_row x y M2 M' l3 ).
      specialize H1 with (i:=#(r - x) : 'I_(S r)) (j:=#(c - y) : 'I_(S c)).
      apply H1 in E3; fin. rewrite E3. 
      pose proof (ElimDown_keep_former_row x M1 M2 #(r - x) #(c - y) l2).
      specialize H4 with (a:=#(r - x) : 'I_(S r)) (b:=#(c - y) : 'I_(S c)).
      apply H4 in E2; fin. rewrite E2; rewrite H2. apply field_1_neq_0.
      apply ElimDown_infer_getcolPivot in E2 as H4; fin.
      pose proof (toREF_keep_getcolPivot x y x M2 M' l3 #(c - y)). apply H1; fin.
    - apply isREF_col_intro. apply IHy in H1; auto; lia.
      pose proof (toREF_keep_getcolPivot (S x) y (S x) M M' l  #(c - y)). 
      apply H2; fin.
  Qed.

  Lemma toREF_isRowPivotOne :
    forall x y {r c} (M M': mat (S r) (S c))  (l : list RowOp),
    x <= S r -> y <= S c -> toREF M x y = (l, M') -> isRowPivotOne M' x y.
  Proof.
    intros x y. generalize dependent x. induction y; intros. 
    1:{ apply isRowPivotOne_col0. } destruct x. 1:{ apply isRowPivotOne_row0. }
    simpl in H1. destruct (getcolPivot M (S x) #(c - y)) as [a|] eqn : E.
    - destruct setPivotAone as [l1 M1] eqn : E1.
      destruct ElimDown as [l2 M2] eqn : E2.
      destruct (toREF M2 x y) as [l3 M3] eqn : E3. 
      injection H1; clear H1; intros. subst; fin.
      apply isRowPivotOne_intro with (j:=#(c - y)).
      + pose proof (toREF_keep_getcolPivot x y x M2 M' l3 #(c - y)).
        apply H1 in E3; fin. clear H1.
        pose proof (ElimDown_infer_getcolPivot x M1 M2 #(r - x) #(c - y) l2).
        apply H1 in E2; fin. clear H1.
        pose proof (setPivotAone_prop (S x) (S y) M M1 a l1).
        apply H1 in E; fin.
      + simpl. replace ((M' #(r - x) #(c - y))) with 1.
        destruct (Aeqdec 1 0) as [E' | E']; auto.
        1:{ pose proof field_1_neq_0. rewrite E' in H1. contradiction. } symmetry.
        pose proof (toREF_keep_former_row x y M2 M' l3).
        specialize H1 with (i:=#(r - x)) (j:=#(c - y)).
        apply H1 in E3; fin. rewrite E3. clear H1.
        pose proof (ElimDown_keep_former_row x M1 M2 #(r - x) #(c - y) l2).
        specialize H1 with (a:=#(r - x)) (b:=#(c - y)).
        apply H1 in E2; fin. rewrite E2; clear H1.
        pose proof (setPivotAone_prop (S x) (S y) M M1 a l1).
        apply H1 in E1; fin.
      + pose proof (toREF_keep_former_row x y M2 M' l3).
        specialize H1 with (i:=#(r - x)) (j:=#(c - y)).
        apply H1 in E3; fin. rewrite E3. clear H1.
        pose proof (ElimDown_keep_former_row x M1 M2 #(r - x) #(c - y) l2).
        specialize H1 with (a:=#(r - x)) (b:=#(c - y)).
        apply H1 in E2; fin. rewrite E2; clear H1.
        pose proof (setPivotAone_prop (S x) (S y) M M1 a l1).
        apply H1 in E1; fin.
      + apply IHy in E3; fin.
    - apply IHy in H1 as H2. apply isRowPivotOne_col_intro; auto. 3: { lia. } 2:{ auto. }
      pose proof (toREF_keep_getcolPivot (S x) y (S x) M M' l #(c - y)).
      apply H3 in H1; fin.
  Qed.

  Lemma toREF_eq : 
    forall (x y : nat) {r c : nat} (M M' : mat (S r) (S c)) (l : list RowOp),
      toREF M x y = (l, M') -> rowOps2mat l * M = M'.
  Proof.
    intros x y. generalize dependent x. induction y; intros.
    destruct x; simpl in H; inv H; simpl; apply mmul_1_l.
    destruct x. simpl in H; inv H; simpl; apply mmul_1_l.
    simpl in H. destruct (getcolPivot M (S x) #(c - y)) as [a|] eqn : E.
    - destruct setPivotAone as [l1 M1] eqn : E1.
      destruct ElimDown as [l2 M2] eqn : E2.
      destruct (toREF M2 x y) as [l3 M3] eqn : E3.
      injection H; clear H; intros. subst.
      apply IHy in E3. rewrite <- E3.
      apply ElimDown_eq in E2. rewrite <- E2.
      apply setPivotAone_eq in E1. rewrite <- E1.
      rewrite !rowOps2mat_app. rewrite <- !mmul_assoc. auto.
    - apply IHy in H. auto.
  Qed. 

  Lemma toREF_rowOpValid :
    forall (x y : nat) {r c : nat} (M M' : mat (S r) (S c)) (l : list RowOp),
      x <= S r -> toREF M x y = (l, M') -> Forall roValid l.
  Proof.
    intros x y. generalize dependent x. induction y; intros.
    destruct x; simpl in H0; inv H0; simpl; auto.
    destruct x; simpl in H0; inv H0; simpl; auto.
    destruct (getcolPivot M (S x) #(c - y)) as [a|] eqn : E.
    - destruct setPivotAone as [l1 M1] eqn : E1.
      destruct ElimDown as [l2 M2] eqn : E2.
      destruct (toREF M2 x y) as [l3 M3] eqn : E3.
      injection H2; clear H2; intros; subst.
      apply Forall_app; split; [|apply Forall_app; split].
      + apply IHy in E3; fin.
      + apply ElimDown_rowOpValid in E2; fin.
      + apply setPivotAone_rowOpValid in E1; fin.
    - apply IHy in H2; auto.    
  Qed.

  Transparent getcolPivot.

  (** 将化为行阶梯的矩阵化为行最简单 *)
  Fixpoint REF2RREF {r c} (M : mat (S r) (S c)) (x : nat) : list RowOp * (mat (S r) (S c)) * nat :=
    match x with
    | O => ([], M, O)
    | S x' =>
      let fx : 'I_(S r) := #x' in
      match getrowPivot M (S c) fx with
      | None => REF2RREF M x'
      | Some a => 
        let '(l1, M1, n') := REF2RREF M x' in
        let (l2, M2) := ElimUp M1 x' fx a in
        ((l2 ++ l1)%list, M2, S n')
      end
    end.

  Opaque getrowPivot.

  Lemma REF2RREF_keep_former_row : 
    forall x {r c} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
      x <= S r -> isRowPivotOne M (S r) (S c) -> REF2RREF M x = (l, M', num) ->
      (forall i : 'I_(S r), x <= i -> M.[i] = M'.[i]).
  Proof.
    induction x; intros.
    - simpl in H1. inv H1; auto.
    - simpl in H1. destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
      + destruct REF2RREF as [[l1 M1] num'] eqn : E1.
        destruct ElimUp as [l2 M2] eqn : E2. inv H1.
        apply IHx with (i:=i) in E1 as H3; fin. rewrite H3.
        pose proof (ElimUp_keep_former_row x M1 M' #x a l2).
        specialize H1 with (a:=i). symmetry ; apply H1; fin.
        unfold isRowPivotOne in H0. replace (M1 #x) with (M #x).
        2:{ apply IHx with (i:=#x) in E1; fin. }
        apply H0; auto; fin.
      + apply IHx with (i:=i) in H1; fin.
  Qed.

  Lemma REF2RREF_keep_isREFandisRowPivotOne :
    forall x {r c} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
      x <= S r -> isREF M (S r) (S c) -> isRowPivotOne M (S r) (S c) ->
      REF2RREF M x = (l, M', num) ->
      isREF M' (S r) (S c) /\ isRowPivotOne M' (S r) (S c).
  Proof.
    induction x; intros.
    - simpl in H2. inv H2. easy.
    - simpl in H2. destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
      + destruct REF2RREF as [[l1 M1] num'] eqn : E1.
        destruct ElimUp as (l2, M2) eqn : E2.
        inv H2. apply IHx in E1 as E3; try easy; try lia. destruct E3 as [H2 H3].
        assert (getrowPivot M1 (S c) #x = Some a).
        { rewrite <- E. apply getrowPivot_same_row. 
          pose proof (REF2RREF_keep_former_row x M M1 l1). specialize H4 with (i:=#x).
          symmetry; apply H4 with num'; fin. } split.
        * pose proof (ElimUp_keep_isREF x M1 M' #x a l2). apply H5 in E2; fin.
          unfold isRowPivotOne in H3. apply H3; fin.
        * pose proof (ElimUp_keep_isRowPivotOne x M1 M' #x a l2). apply H5 in E2; fin.
      + apply IHx in H2; fin.
  Qed. 

  Lemma REF2RREF_isbothPivot :
    forall x {r c} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat) ,
    x <= S r ->
    isREF M (S r) (S c) -> isRowPivotOne M (S r) (S c) ->
    REF2RREF M x = (l, M', num) -> isbothPivot M' x.
  Proof.
    induction x; intros. 1:{ apply isbothPivot_row0. }
    apply isbothPivot_intro; intros.
    - clear IHx. simpl in H2. destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
      + inv H3. destruct REF2RREF as [[l1 M1] num'] eqn : E1.
        destruct ElimUp as [l2 M2] eqn : E2. inv H2.
        pose proof (REF2RREF_keep_isREFandisRowPivotOne x M M1 l1).
        apply H2 in E1 as H3; fin. clear H2. destruct H3 as [H2 H3].
        assert (getrowPivot M1 (S c) #x = Some a).
        { rewrite <- E. apply getrowPivot_same_row.
          pose proof (REF2RREF_keep_former_row x M M1 l1).
          specialize H4 with (i:=#x). apply H4 in E1; fin. }
        assert (getrowPivot M' (S c) #x = Some a).
        { rewrite <- H4. apply getrowPivot_same_row.
          pose proof (ElimUp_keep_former_row x M1 M' #x a l2).
          specialize H6 with (a:=#x). apply H6 in E2; fin.
          unfold isRowPivotOne in H3. apply H3; fin. }
        rewrite H5 in H6; inv H6.
        pose proof (ElimUp_infer_getcolPivot M1 M' #x a l2).
        rewrite fin2nat_nat2finS in H6. apply H6 in E2; fin.
        1:{ unfold isRowPivotOne in H3; apply H3; fin. } lia.
      + assert (getrowPivot M' (S c) #x = None).
        { rewrite <- E. apply getrowPivot_same_row.
          pose proof (REF2RREF_keep_former_row x M M' l).
          specialize H4 with (i:=#x). apply H4 in H2; fin. }
        rewrite H3 in H4; inv H4.
    - simpl in H2. destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
      + destruct REF2RREF as [[l1 M1] num'] eqn : E1.
        destruct ElimUp as [l2 M2] eqn : E2. inv H2.
        apply IHx in E1 as H2; fin; clear IHx. 
        pose proof (ElimUp_keep_isbothPivot x x M1 M' l2 #x a).
        apply H3 in E2; fin; clear H3.
        * pose proof (REF2RREF_keep_isREFandisRowPivotOne x M M1 l1).
          apply H3 in E1; fin.
        * rewrite <- E. apply getrowPivot_same_row.
          pose proof (REF2RREF_keep_former_row x M M1 l1).
          specialize H3 with (i:=#x). symmetry; apply H3 with num'; fin.
      + apply IHx in H2; fin.
  Qed.

  Lemma REF2RREF_eq : 
    forall (x : nat) {r c : nat} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
      REF2RREF M x = (l, M', num) -> rowOps2mat l * M = M'.
  Proof.
    induction x; intros. 1:{ inv H. simpl; apply mmul_1_l. }
    simpl in H. destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
    - destruct REF2RREF as [[l1 M1] num'] eqn : E1.
      destruct ElimUp as [l2 M2] eqn : E2. inv H.
      rewrite !rowOps2mat_app. rewrite mmul_assoc.
      apply IHx in E1. rewrite E1. apply ElimUp_eq in E2. auto.
    - apply IHx in H. auto. 
  Qed.

  Lemma REF2RREF_rowOpValid :
    forall (x : nat) {r c : nat} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
      x <= S r -> REF2RREF M x = (l, M', num) -> Forall roValid l.
  Proof.
    induction x; intros. 1:{ simpl in H0. inv H0. auto. }
    simpl in H0. destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
    - destruct REF2RREF as [[l1 M1] num'] eqn : E1. destruct ElimUp as [l2 M2] eqn : E2.
      inv H0. rewrite Forall_app. split.
      + apply ElimUp_rowOpValid in E2; auto; fin.  
      + apply IHx in E1; fin.
    - apply IHx in H0; fin. 
  Qed.


  Transparent getrowPivot.

  (** 将一般矩阵转为行最简矩阵 *)
  Definition toRREF {r c} (M : mat (S r) (S c)) : list RowOp * (mat (S r) (S c)) * nat :=
    let (l1, M1) := toREF M (S r) (S c) in
    let '(l2, M2, num) := REF2RREF M1 (S r) in
    ((l2 ++ l1)%list, M2, num).

  Theorem toRREF_isRREF :
    forall {r c} (M M': mat (S r) (S c)) (l : list RowOp) (num : nat),
    toRREF M = (l, M', num) -> isRREF M'.
  Proof.
    intros. unfold toRREF in H. 
    destruct toREF as (l1, M1) eqn : E.
    destruct REF2RREF as [[l2 M2] num'] eqn : E'. inv H.
    unfold isRREF. apply and_assoc; split.
    - pose proof (REF2RREF_keep_isREFandisRowPivotOne (S r) M1 M' l2 num). apply H; fin.
      * pose proof (toREF_isREF (S r) (S c) M M1 l1). apply H0; fin.
      * pose proof (toREF_isRowPivotOne (S r) (S c) M M1 l1). apply H0; fin.
    - pose proof (REF2RREF_isbothPivot (S r) M1 M' l2). apply H in E'; fin.
      * pose proof (toREF_isREF (S r) (S c) M M1 l1). apply H0 in E; fin.
      * pose proof (toREF_isRowPivotOne (S r) (S c) M M1 l1). apply H0 in E; fin.
  Qed.

  Lemma toRREF_eq :
    forall {r c : nat} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
      toRREF M = (l, M', num) -> rowOps2mat l * M = M'.
  Proof.
    intros. unfold toRREF in H.
    destruct toREF as [l1 M1] eqn : E1. destruct REF2RREF as [[l2 M2] num'] eqn : E2.
    inv H. rewrite rowOps2mat_app. apply toREF_eq in E1. apply REF2RREF_eq in E2.
    rewrite mmul_assoc. rewrite E1. apply E2.
  Qed.

  Lemma toRREF_rowOpValid :
      forall {r c : nat} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
      toRREF M = (l, M', num) -> Forall roValid l.
  Proof.
    intros. unfold toRREF in H.
    destruct toREF as [l1 M1] eqn : E1. destruct REF2RREF as [[l2 M2] num'] eqn : E2.
    inv H. rewrite Forall_app. split.
    - apply REF2RREF_rowOpValid in E2; auto.
    - apply toREF_rowOpValid in E1; auto.  
  Qed.

  Fixpoint getPivotNum {r c : nat} (M : mat (S r) (S c)) (x : nat) : nat :=
    match x with
    | O => O
    | S x' =>
      let fx : 'I_(S r) := #x' in
      match getrowPivot M (S c) fx with
      | None => getPivotNum M x'
      | Some a => S (getPivotNum M x')
      end
    end.

       Theorem existisREFByMRT : forall {r c} (M : mat (S r) (S c)),
    exists N : mat (S r) (S c), MRT M N /\ isREF N (S r) (S c).
  Proof.
    intros. destruct (toREF M (S r) (S c)) as [l N] eqn : E. exists N; split.
    - apply MRT_RowOp. exists l. split.
      apply toREF_rowOpValid in E; auto. apply toREF_eq in E; auto.
    -  apply toREF_isREF in E; fin. 
  Qed.

  Theorem existisRREFbyMRT : forall {r c} (M : mat (S r) (S c)),
    exists N : mat (S r) (S c), MRT M N /\ isRREF N.
  Proof.
    intros. destruct (toRREF M) as [[l N] num] eqn : E. exists N; split.
    - apply MRT_RowOp. exists l. split.
      apply toRREF_rowOpValid in E; auto. apply toRREF_eq in E; auto.
    -  apply toRREF_isRREF in E; fin. 
  Qed.
  

  Opaque getrowPivot.

    Lemma vinsert_mcol :
    forall {r c} (M : mat r c) i j val,
    (vinsert M i val)&[j] = (vinsert M&[j] i val.[j]).
  Proof.
    intros. extensionality x. unfold mcol.
    destruct (x ??< i); [|destruct (i ??< x)].
    - erewrite !vnth_vinsert_lt. auto. Unshelve. all : fin.
    - erewrite !vnth_vinsert_gt. auto. Unshelve. all : fin.
    - assert (i <= x) by lia. assert (x <= i) by lia. clear n n0.
      assert (fin2nat i = fin2nat x) by lia. apply fin2nat_eq_iff in H1; subst.
      erewrite !vnth_vinsert_eq. auto. Unshelve. all : fin.
  Qed.

  Lemma vremove_mcol :
    forall {r c} (M : mat (S r) c) i j,
    (vremove M i)&[j] = (vremove M&[j] i).
  Proof.
    intros. extensionality x. unfold mcol.
    destruct (x ??< i).
    - erewrite !vnth_vremove_lt. erewrite !nth_v2f. auto. Unshelve. all : fin.
    - erewrite !vnth_vremove_ge. erewrite !nth_v2f. auto. Unshelve. all : fin.
  Qed.

  Lemma vset_mcol :
    forall {r c} (M : mat r c) i j val,
    (vset M i val)&[j] = (vset M&[j] i val.[j]).
  Proof.
    intros. extensionality x. unfold mcol.
    unfold vset. destruct (x ??= i); auto.
  Qed.

  Lemma getPivotNum_le :
    forall {r c} (M : mat (S r) (S c)) x,
      getPivotNum M x <= x.
  Proof.
    intros. induction x.
    - simpl; auto.
    - simpl. destruct (getrowPivot M (S c) #x ).
      + lia. + lia.
  Qed.

  Lemma getPivotNum_Some_le :
    forall {r c} (M : mat (S r) (S c)),
    getPivotNum M (S r) <= S r.
  Proof.
    intros. apply getPivotNum_le.
  Qed.

  Lemma mrowAdd_keep_getrowPivot : 
  forall {r c} (M : mat (S r) (S c)) (i i' : 'I_(S r)) (j : 'I_(S r)) (k : tA),
    i' < i -> j < i -> isREF M (S r) (S c) ->
    getrowPivot M (S c) j = getrowPivot (mrowAdd i' i k M) (S c) j.
  Proof.
    intros. pose proof (getrowPivot_dec (S c) M j). destruct H2.
    - destruct e as [a H2].
      apply getrowPivot_eq_Some in H2 as H3. destruct H3 as [_ [H3 H4]].
      assert (forall j' : 'I_(S c), j' <= a -> M.[i].[j'] = 0).
      { intros. pose proof (isREF_row_Some (S r) (S c) M j a).
        specialize H6 with (i':=i) (j':=j'). apply H6; fin. } rewrite H2; symmetry. 
      apply getrowPivot_eq_Some. repeat split; fin.
      + unfold mrowAdd. destruct (j ??= i'); fin. replace (M i a) with 0.
        replace ((M j a + k * 0)%A) with (M j a) by fin. auto.
        symmetry. apply H5; fin.
      + unfold mrowAdd. replace (M j j0) with 0. replace (M i j0) with 0.
        destruct (j ??= i'); fin. all : symmetry. apply H5; fin.
        apply H4; fin.
    - rename e into H2. assert (H3 := H2).
      rewrite getrowPivot_eq_None in H3.
      assert (forall j' : 'I_(S c), M.[i].[j'] = 0).
      { intros. pose proof (isREF_row_None (S r) (S c) M j).
        specialize H4 with (i':=i) (j':=j'). apply H4; fin. } rewrite H2; symmetry. 
       apply getrowPivot_eq_None. repeat split; fin.
       unfold mrowAdd. replace (M j j0)%A with 0. replace (M i j0)%A with 0.
       destruct (j??=i'); fin. all : symmetry.
       apply H4; auto. apply H3; auto.
  Qed.

  Lemma mrowAdd_keep_getPivotNum : 
  forall x {r c} (M : mat (S r) (S c)) (i i' : 'I_(S r))  (k : tA),
    i' < i -> x <= i -> isREF M (S r) (S c) ->
    getPivotNum M x = getPivotNum (mrowAdd i' i k M) x.
  Proof.
    induction x; intros; auto. simpl.
    assert (Ex : x < S r). {pose proof (fin2nat_lt i); lia. }
    replace (getrowPivot (mrowAdd i' i k M) (S c) #x) with (getrowPivot M (S c) #x).
    apply IHx with (i':=i') (i:=i) (k:=k) in H1; fin. rewrite <- !H1. auto.
    apply mrowAdd_keep_getrowPivot; fin.
  Qed.

  Lemma ElimUp_keep_getrowPivot : 
  forall x {r c} (M M': mat (S r) (S c)) (l : list RowOp) (i j: 'I_(S r)) (a : 'I_(S c)),
    x < i -> j < i -> isREF M (S r) (S c) -> 
    getrowPivot M (S c) i = Some a -> ElimUp M x i a = (l, M') ->
    getrowPivot M (S c) j = getrowPivot M' (S c) j.
  Proof.
    induction x; intros. inv H3. auto. simpl in H3.
    assert (Ex : x < S r). {pose proof (fin2nat_lt i); lia. }
    destruct (Aeqdec (M #x a) 0) as [E|E].
    - apply IHx with (j:=j) in H3; fin.
    - destruct ElimUp as [l2 M2] eqn : E1. inv H3. apply IHx with (j:=j) in E1 as H3; fin.
      rewrite <- H3. apply mrowAdd_keep_getrowPivot; fin.
      + pose proof (mrowAdd_keep_isREF (S r) (S c) M i #x (- M #x a)). apply H3; fin.
      + rewrite <- H2; symmetry. apply getrowPivot_same_row. extensionality b. 
        unfold mrowAdd. destruct (i ??= #x); fin.
  Qed.

  Lemma ElimUp_keep_getPivotNum :
    forall x {r c} (M M' : mat (S r) (S c)) (l : list RowOp) (i : 'I_(S r)) (a : 'I_(S c)),
      x <= i -> isREF M (S r) (S c) -> 
      getrowPivot M (S c) i = Some a -> M i a = 1 ->
      ElimUp M x i a = (l, M') ->
      getPivotNum M x = getPivotNum M' x.
  Proof.
    induction x; intros. auto. simpl. simpl in H3. 
    assert (Ex : x < S r). {pose proof (fin2nat_lt i); lia. }
    destruct (Aeqdec (M #x a) 0) as [E|E].
    - apply IHx in H3 as H4; fin. rewrite <- H4. 
      replace (getrowPivot M' (S c) #x) with (getrowPivot M (S c) #x); auto.
      apply getrowPivot_same_row. pose proof (ElimUp_keep_former_row x M M' i a l).
      specialize H5 with #x. symmetry; apply H5; fin.
    -  destruct ElimUp as [l2 M2] eqn : E1. injection H3; intros. subst M2. subst l. clear H3.
      apply IHx in E1 as H3;fin. replace (getrowPivot M' (S c) #x) with (getrowPivot M (S c) #x).
      replace (getPivotNum M x) with (getPivotNum (mrowAdd #x i (- M #x a) M) x).
      * rewrite H3; auto.
      * symmetry. apply mrowAdd_keep_getPivotNum; fin.
      * apply eq_trans with (getrowPivot (mrowAdd #x i (- M #x a) M) (S c) #x).
        apply mrowAdd_keep_getrowPivot; fin. apply ElimUp_keep_getrowPivot with (j:=#x) in E1; fin.
        pose proof (mrowAdd_keep_isREF (S r) (S c) M i #x (- M #x a)). apply H4; fin.
        rewrite <- H1. symmetry. apply getrowPivot_same_row. extensionality b. 
        unfold mrowAdd. destruct (i ??= #x); fin.
      * pose proof (mrowAdd_keep_isREF (S r) (S c) M i #x (- M #x a)). apply H3; fin.
      * rewrite <- H1. symmetry. apply getrowPivot_same_row. extensionality b. 
        unfold mrowAdd. destruct (i ??= #x); fin.
      * unfold mrowAdd. destruct (i ??= #x); fin.
  Qed.




  Lemma REF2RREF_keep_getrowPivot : 
  forall x {r c} (M M': mat (S r) (S c)) (l : list RowOp) (j: 'I_(S r)) (num : nat),
    x <= j -> isREF M (S r) (S c) -> isRowPivotOne M (S r) (S c) ->
    REF2RREF M x = (l, M', num) ->
    getrowPivot M (S c) j = getrowPivot M' (S c) j.
  Proof.
    induction x; intros. inv H2; auto. simpl in H2.
    assert (x < S r). {pose proof (fin2nat_lt j). fin. }
    destruct (getrowPivot M (S c) #x) as [b|] eqn : E.
    - destruct REF2RREF as [[l1 M1] num'] eqn : E1.
      destruct ElimUp as [l2 M2] eqn : E2. inv H2. apply IHx with (j:=j) in E1 as H4; fin.
      rewrite H4. apply getrowPivot_same_row. pose proof (ElimUp_keep_former_row x M1 M' #x b l2).
      specialize H2 with j. symmetry; apply H2; fin.
      apply REF2RREF_keep_former_row with (i:=#x) in E1; fin. rewrite <- E1.
      unfold isRowPivotOne in H1. apply H1; fin.
    - apply IHx with (j:=j) in H2; fin. 
  Qed.

      
  Lemma getPivotNum_REF2RREF :
    forall x {r c} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
    x <= S r -> isREF M (S r) (S c) -> isRowPivotOne M (S r) (S c) -> REF2RREF M x = (l, M', num) -> getPivotNum M' x = num.
  Proof.
    induction x; intros.
    - simpl in *. injection H2; clear H2; intros. auto.
    - simpl in *. destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
      + destruct REF2RREF as [[l1 M1] num'] eqn : E1.
        destruct ElimUp as [l2 M2] eqn : E2. inv H2.
        assert (M #x = M1 #x).
        { pose proof (REF2RREF_keep_former_row x M M1 l1 num').
          specialize H2 with (i:=#x). apply H2; fin. }
        assert (M1 #x a = 1).
        { rewrite <- H2. unfold isRowPivotOne in H1. apply H1; fin. }   
        assert (getrowPivot M1 (S c) #x = getrowPivot M (S c) #x).
        { apply getrowPivot_same_row. symmetry. auto.  }
        assert (M1 #x = M' #x).
        { pose proof (ElimUp_keep_former_row x M1 M' #x a l2).
          specialize H5 with (a:=#x). symmetry; apply H5; fin. }
        assert (getrowPivot M' (S c) #x = getrowPivot M1 (S c) #x).
        { apply getrowPivot_same_row. symmetry; auto. } 
        rewrite H6. rewrite H4. rewrite E. apply IHx in E1 as H7; fin.
        apply ElimUp_keep_getPivotNum in E2 as H8; fin.
        apply REF2RREF_keep_isREFandisRowPivotOne in E1; fin.
        rewrite <- E. apply REF2RREF_keep_getrowPivot with (j:=#x) in E1; fin.
      + apply IHx in H2 as H3; fin. replace (getrowPivot M' (S c) #x) with (getrowPivot M (S c) #x).
        rewrite E; auto. apply REF2RREF_keep_getrowPivot with (j:=#x) in H2; fin.
  Qed.

  Lemma getPivotNum_toRREF :
    forall {r c} (M M' : mat (S r) (S c)) (l : list RowOp) (num : nat),
    toRREF M = (l, M', num) -> getPivotNum M' (S r) = num.
  Proof.
    intros. unfold toRREF in H.
    destruct toREF as [l1 M1] eqn : E1. destruct REF2RREF as [[l2 M2] num'] eqn : E2.
    inv H. apply getPivotNum_REF2RREF in E2; auto.
    apply toREF_isREF in E1; fin. apply toREF_isRowPivotOne in E1; fin.
  Qed.

  Lemma getPivotNum_0:
    forall  x {r c} (M : mat (S r) (S c)),
    S x <= S r -> isREF M (S r) (S c) -> getPivotNum M (S x) = O ->
    forall i, M i = vzero.
  Proof.
    induction x; intros.
    - simpl in H1. destruct (getrowPivot M (S c) #0) as [a|] eqn : E.
      inv H1. apply NNPP. intro. rewrite vneq_vzero in H2. destruct H2 as [a H2].
      destruct ((i ??= O)).
      + apply H2. assert (i = #0). { apply fin2nat_eq_iff. rewrite fin2nat_nat2finS; fin. }
        subst. rewrite getrowPivot_eq_None in E. apply E; fin.
      + pose proof (getrowPivot_neqzero (S c) M i a). destruct H3; fin.
        destruct H3. unfold isREF in H0. specialize H0 with (i:=#0) (j:=i).
        assert (rpivotlt (getrowPivot M (S c) #0) (getrowPivot M (S c) i)).
        { apply H0; fin. } unfold rpivotlt in H5.
        rewrite E in H5. rewrite H3 in H5. auto.
    - simpl in H1. destruct (getrowPivot M (S c) #(S x)) as [a|] eqn : E.
      inv H1. apply IHx with (i:=i) in H1; fin.
  Qed.

  Lemma isREF_getPivotNum :
    forall x  {r c} (M : mat (S r) (S c)) a,
    x < S r -> isREF M (S r) (S c) -> 
    getrowPivot M (S c) #x = Some a ->
    getPivotNum M (S x) = S x.
  Proof.
    induction x; intros.
    - simpl. rewrite H1. auto.
    - simpl. rewrite H1. fin. 
    destruct  (getrowPivot M (S c) #x) as [b|] eqn : E.
    + fin. apply IHx in E as H2; fin. simpl in H2.
      rewrite E in H2. auto.
    + unfold isREF in H0. specialize H0 with (i:=#x) (j:=#(S x)).
      rewrite H1 in H0. rewrite E in H0. destruct H0; fin.
  Qed.


  Lemma getPivotNum_Some :
    forall n x {r c} (M : mat (S r) (S c))  ,
    x <= S r -> isREF M (S r) (S c) -> getPivotNum M x = S n ->
    forall i : 'I_(S n), 
    exists b : 'I_(S c), getrowPivot (fun a : 'I_(S n) => M #a) (S c) i = Some b.
  Proof.
    induction n.
    - induction x; intros.
      + inv H1.
      + assert (fin2nat i = O). { pose proof (fin2nat_lt i). fin. } 
        assert (i = #0) by fin; subst. clear H2. destruct x.
        * simpl in H1. destruct (getrowPivot M (S c) #0) as [a|] eqn : E.
          ** exists a. apply getrowPivot_eq_Some in E. destruct E as [_ [H2 H3]].
            apply getrowPivot_eq_Some. repeat split; fin.
          ** inv H1.
        * simpl in H1. destruct (getrowPivot M (S c) #(S x)) eqn : E1.
          ** destruct (getrowPivot M (S c) #x) eqn : E2.
             *** inv H1.
             *** unfold isREF in H0. specialize H0 with (i:=#x) (j:=#(S x)).
                 rewrite E1 in H0; rewrite E2 in H0. destruct H0; fin.
          ** apply IHx with (i:=#0) in H1; fin.
    - induction x; intros.
      + inv H1.
      + assert (H2:= H1). simpl in H1. destruct (getrowPivot M (S c) #x) as [a'|] eqn : E1.
        * assert (x = S n). { pose proof (isREF_getPivotNum x M a'). erewrite H3 in H2; fin. }
          subst. apply eq_add_S in H1.
          destruct (i ??= S n).
          ** assert ((#i : 'I_(S r)) = (#(S n) : 'I_(S r))) by fin.
             exists a'. apply getrowPivot_eq_Some in E1. destruct E1 as [_ [H4 H5]].
             apply getrowPivot_eq_Some. repeat split; fin.
          ** assert (i < S n). {pose proof (fin2nat_lt i). fin. }
             apply IHn with (i:=fPredRange i H3) in H1; fin. destruct H1 as [b H1].
             exists b. apply getrowPivot_eq_Some in H1. destruct H1 as [_ [H4 H5]].
             apply getrowPivot_eq_Some. repeat split; fin.
        * apply IHx with (i:=i) in H1; fin.  
  Qed.

  Lemma getPivotNum_prop :
    forall {r c} (M : mat (S r) (S c)) n i,
    isRREF M -> getPivotNum M (S r) = S n ->
    exists b : 'I_(S c), getrowPivot (fun a : 'I_(S n) => M #a) (S c) i = Some b /\ 
    (fun a : 'I_(S n) => M #a)&[b] = veye #(fin2nat i).
  Proof.
    intros. assert (Enr : n <= r).
    { pose proof (getPivotNum_le M (S r)). rewrite H0 in H1. lia. }
    assert (H1 := H). destruct H as [H2 [H3 H4]].
    pose proof (getPivotNum_Some n (S r) M). specialize H with (i:=i).
    destruct H; fin. exists x. split; auto. extensionality y.
    unfold mcol. assert (getrowPivot M (S c) #i = Some x).
    { apply getrowPivot_eq_Some in H. destruct H as [H [H5 H6]].
      apply getrowPivot_eq_Some. repeat split; fin. }
    pose proof (isRREF_col_veye M #i x).
    apply H6 in H1; auto. replace (M #y x) with (M&[x] #y) by fin. rewrite H1.
    assert (i < S r). {pose proof (fin2nat_lt i). lia. }
    assert (y < S r). {pose proof (fin2nat_lt y). lia. }
    unfold veye. rewrite !fin2nat_nat2finS; auto; try rewrite fin2nat_nat2finS; fin.
  Qed.

  Lemma getPivotNum_ascend :
    forall {r c} (M : mat (S r) (S c)) x x',
    x <= x' -> getPivotNum M x <= getPivotNum M x'.
  Proof.
    intros. induction H. auto. apply Nat.le_trans with (getPivotNum M m).
    auto. simpl. destruct (getrowPivot M (S c) #m); fin.
  Qed.

  Lemma getPivotNum_None :
    forall {r c} (M : mat (S r) (S c)) n (i : 'I_(S r)),
    n <= i -> isREF M (S r) (S c) -> getPivotNum M (S r) = n ->
    M.[i] = vzero.
  Proof.
    intros. apply NNPP; intro. rewrite vneq_vzero in H2.
    destruct H2 as [a H2]. pose proof (getrowPivot_neqzero (S c) M i a).
    destruct H3 as [b [H3 H4]]; fin. assert (getPivotNum M (S i) = S i).
    { pose proof (isREF_getPivotNum i M b). apply H5; fin. }
    pose proof (getPivotNum_ascend M (S i) (S r)). assert (S i <= S r).
    { pose proof (fin2nat_lt i). lia. } apply H6 in H7. rewrite H1 in H7.
    rewrite H5 in H7. lia.
  Qed. 

  Lemma getPivotNum_exists_veye :
    forall {r c} (M : mat (S r) (S c))  (i : 'I_(S r)),
    isRREF M -> i < getPivotNum M (S r) -> exists j : 'I_(S c), M&[j] = veye i.
  Proof.
    intros. destruct (getPivotNum M (S r)) as [|n] eqn : E. lia.
    pose proof  (getPivotNum_prop M n #i). apply H1 in E; fin.
    clear H1. destruct E as [j [H2 H3]]. exists j.
    assert (getrowPivot M (S c) i = Some j).
    { rewrite getrowPivot_eq_Some in H2. destruct H2 as [H2 [H4 H5]].
      rewrite getrowPivot_eq_Some. repeat split; fin. }
    apply isRREF_col_veye in H1; fin.
  Qed.

  Fixpoint getPivotNum_strict {r c} (M : mat (S r) (S c)) (x : nat) (y : nat) : nat := 
    match x, y with
    | O, _=> O
    | _, O => O
    | S x', S y' =>
      let fx : 'I_(S r) := #x' in
      match getrowPivot M (S c) fx with
      | None => getPivotNum_strict M x' y
      | Some a => if (a ??< y) then S (getPivotNum_strict M x' a) else getPivotNum_strict M x' y
      end
    end.

  Lemma getPivotNum_strict_eq :
    forall x {r c} (M : mat (S r) (S c)),
    x <= S r -> isRREF M -> getPivotNum M x = getPivotNum_strict M x (S c).
  Proof.
    induction x; intros. simpl; auto. simpl. 
    destruct (getrowPivot M (S c) #x) as [a|] eqn : E.
    - pose proof (fin2nat_lt a). destruct (a ??< S c); fin.
      assert (x <= S r) by lia. pose proof (IHx _ _ _ H2 H0).
      clear H2; clear IHx.  rewrite H3. clear H3.
      destruct H0 as [H0 _]. unfold isREF in H0.
      destruct x. simpl. auto. specialize H0 with (i:=#x) (j:=#(S x)).
      assert (rpivotlt (getrowPivot M (S c) #x) (Some a)).
      { rewrite <- E. apply H0; fin. }
      destruct (getrowPivot M (S c) #x) as [b|] eqn : E'.
      simpl in H2. simpl. destruct (fin2nat a). lia.
      rewrite E'. fin. simpl in H2; fin.
    - apply IHx; fin.
  Qed.

  Lemma getPivotNum_strict_le :
    forall x y {r c} (M : mat (S r) (S c)),
    getPivotNum_strict M x y <= y.
  Proof.
    induction x; intros.
    - simpl; fin.
    - simpl. destruct y; fin. destruct (getrowPivot M (S c) #x).
      + destruct (f ??< S y).
        * apply le_n_S. pose proof (IHx f _ _ M). fin.
        * apply IHx.
      + apply IHx.
  Qed.
  
  Lemma getPivotNum_col_le :
    forall  {r c} (M : mat (S r) (S c)),
    isRREF M -> getPivotNum M (S r) <= S c.
  Proof.
    intros. pose proof (getPivotNum_strict_eq (S r) M).  
    rewrite H0; fin. apply getPivotNum_strict_le.
  Qed.

  Lemma getPivotNum_col_lt_row :
    forall  {r c} (M : mat (S r) (S c)),
    isRREF M -> c < r -> M.[#r] = vzero.
  Proof.
    intros. pose proof (getPivotNum_None M (getPivotNum M (S r)) #r).
    apply H1; fin. pose proof (getPivotNum_col_le M). apply H2 in H. lia.
    destruct H; fin.
  Qed.






End GaussElim.
