(*
  Copyright 2025 Zhou Kangqi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : System of Linear Equations (or Linear Equations)
  author    : Zhou Kangqi
  date      : 2025.08

  reference :
  1. https://en.wikipedia.org/wiki/System_of_linear_equations

  remark    :
  1. 一些记号：线性方程组的初等变换；或者矩阵的行变换
     [j] + [i] * K   : 第i个方程的K倍加到第j个方程; 第i行的K倍加到第j行
     ([i], [j])      : 交换第i个方程和第j个方程; 交换第i行和第j行
     [i] * K         : 第i个方程乘以非零数K; 第i行乘以非零数k
  2. 为了保持方程组初等变换前后同解，对以上变换有如下要求
     [j] + [i] * K   : 要求 i 和 j 不同
     [i] * K         : 要求 K 非零
 *)

Require Export MatrixGauss.

(** * System of Linear Equations (线性方程组) *)
Section SystemOfLinearEquations.
  Context `{HField : Field}.
  Context {AeqDec : Dec (@eq tA)}.
  Add Field field_inst : (make_field_theory HField).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (-b)).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * / b). 
  Infix "/" := Adiv : A_scope.
  
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation vdot := (@vdot _ Aadd 0 Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.
  Notation vscal := (@vscal _ Amul).
  Notation "x \.* a" := (vscal x a) : vec_scope.
  Notation vzero := (vzero Azero).
  Notation l2v := (@l2v _ Azero).
  Notation vopp := (@vopp _ Aopp).
  
  Notation mat r c := (mat tA r c).
  Notation mat1  := (@mat1 tA Azero Aone).
  Notation mrowSwap := (@mrowSwap tA).
  Notation mrowScale := (@mrowScale _ Amul).
  Notation mrowAdd := (@mrowAdd _ Aadd Amul).

  Notation isREF := (@isREF _ Azero _).
  Notation getrowPivot := (getrowPivot (Azero:=0)).
  Notation getcolPivot := (getcolPivot (Azero:=0)).
  Notation sm2REF := (@sm2REF _ Aadd 0 Aopp Amul Ainv _).
  Notation sm2RREF := (@sm2RREF _ Aadd 0 Aopp Amul _).
  Notation toREF := (@toREF _ Aadd 0 Aopp Amul Ainv _).
  Notation rowOps2mat := (@rowOps2mat tA Aadd Azero Amul Aone).
  Notation rowOps2matInv := (@rowOps2matInv _ Aadd 0 Aopp Amul 1 Ainv).
  Notation mmul := (@mmul tA Aadd 0 Amul).
  Notation mmulv := (@mmulv tA Aadd 0 Amul).

  Notation roValid := (@roValid tA Azero).
  Infix "*" := mmul : mat_scope.
  Infix "*v" := mmulv : mat_scope.

  Notation lrep := (@lrep _ _ vadd vzero vscal).
  Notation lreps := (@lreps _ _ vadd vzero vscal).
  Notation ldep := (@ldep _ Azero _ vadd vzero vscal).
  Notation lindep := (@lindep _ Azero _ vadd vzero vscal).
  Notation vsequiv := (@vsequiv _ _ vadd vzero vscal).

  (** *** 线性方程（简称方程） *)
    
    (* n元线性方程，由系数和常数项构成 *)
  Definition Eqn (n : nat) := (@vec tA n * tA)%type.

    (* 两个方程相加 *)
  Definition eqnAdd {n} (e1 e2 : Eqn n) : Eqn n :=
    (fst e1 + fst e2, (snd e1 + snd e2)%A).

    (* e1 + e2 = e2 + e1 *)
  Lemma eqnAdd_comm : forall {n} (e1 e2 : Eqn n),
    eqnAdd e1 e2 = eqnAdd e2 e1.
  Proof. intros. unfold eqnAdd. simpl. f_equal; apply commutative.
  Qed.

    (* e1 + (e2 + e3) = (e1 + e2) + e3 *)
  Lemma eqnAdd_assoc : forall {n} (e1 e2 e3 : Eqn n),
    eqnAdd e1 (eqnAdd e2 e3) = eqnAdd (eqnAdd e1 e2) e3.
  Proof. intros. unfold eqnAdd; simpl. pose proof (vadd_AMonoid n). f_equal;  amonoid. Qed.

    (* 方程乘以K倍 *)
  Definition eqnK {n} (K : tA) (e : Eqn n) : Eqn n :=
    (K \.* fst e, K * snd e)%A.

  Lemma eqnK_add : forall {n} (e : Eqn n) (K1 K2 : tA),
    eqnK (K1 + K2)%A e = eqnAdd (eqnK K1 e) (eqnK K2 e).
  Proof.
    intros. unfold eqnK, eqnAdd; simpl. f_equal.
    - rewrite vscal_add. auto.
    - ring.
  Qed.

  (** *** 线性方程组（简称方程组） *)
    (* A general system of `s` linear equations with `n` unknowns and coefficents.
       Often the coefficents and unknowns are real or complex numbers, but integers 
       and rational numbers are also seen, as are polynomials and elements of an 
       abstract algebraic structure. *)

    (* 含有s个方程的n元线性方程组 *)
  Definition Eqns (n s : nat) := (@vec (@vec tA s) n * (@vec tA s))%type.


  (** *** 方程组初等变换之交换两行 *)

    (* 方程组第i和j两行交换，记作 ([i], [j]) *)
  Definition eqnsSwap {n s} (e : Eqns n s) (i j : 'I_s) : Eqns n s := vswap e i j.

    Lemma eqnsSwap_eqnsSwap : forall {n s} (e : Eqns n s) (i j : fin s),
        eqnsSwap (eqnsSwap e i j) j i = e.
    Proof. intros. unfold eqnsSwap. apply vswap_vswap. Qed.

  End eqnsSwap.

  (** *** 方程组初等变换之某行乘以非零常数 *)
  Section eqnsScale.
    
    (* 方程组第i行乘以K，记作 [i] * K。注：要求k非零 *)
    Definition eqnsScale {n s} (e : Eqns n s) (i : fin s) (K : tA) : Eqns n s :=
      fun j => if j ??= i then (K \.* fst e.[j], K * snd e.[j]) else e.[j].

    Lemma eqnsScale_1 : forall {n s} (e : Eqns n s) (i : fin s), eqnsScale e i 1 = e.
    Proof.
      intros. unfold eqnsScale. apply veq_iff_vnth; intros j.
      destruct (_??=_); subst; auto.
      rewrite vscal_1_l, identityLeft. rewrite <- surjective_pairing; auto.
    Qed.
      
    Lemma eqnsScale_eqnsScale : forall {n s} (e : Eqns n s) (i : fin s) (K1 K2 : tA),
        eqnsScale (eqnsScale e i K1) i K2 = eqnsScale e i (K1*K2).
    Proof.
      intros. unfold eqnsScale. apply veq_iff_vnth; intros j.
      destruct (_??=_); subst; auto; simpl. f_equal.
      - rewrite vscal_assoc; f_equal. ring.
      - ring.
    Qed.
  End eqnsScale.

  (** *** 方程组初等变换之某行乘以倍数后加至另一行 *)
  Section eqnsAdd.
    
    (* 方程组第i行乘以K加到第j行，记作 [i] + [j] * K。注：要求i和j不同 *)
    Definition eqnsAdd {n s} (e : Eqns n s) (i j : fin s) (K : tA) : Eqns n s :=
      fun k => if k ??= i then eqnAdd e.[i] (eqnK K e.[j])  else e.[k].

    Lemma eqnsAdd_K0 : forall {n s} (e : Eqns n s) (i j : fin s), eqnsAdd e i j 0 = e.
    Proof.
      intros. apply veq_iff_vnth; intros k.
      unfold eqnsAdd. destruct (_??=_); try (apply fin2nat_eq_iff in e0; subst); auto.
      unfold eqnAdd, eqnK. simpl. rewrite vscal_0_l. rewrite ring_mul_0_l at 1.
      rewrite !identityRight. rewrite <- surjective_pairing; auto.
    Qed.

    Lemma eqnsAdd_eqnsAdd : forall {n s} (e : Eqns n s) (i j : 'I_s) (K1 K2 : tA),
        i <> j -> eqnsAdd (eqnsAdd e i j K1) i j K2 = eqnsAdd e i j (K1+K2)%A.
    Proof.
      intros. apply veq_iff_vnth; intros k. unfold eqnsAdd. 
      apply fin2nat_neq_iff in H.
      destruct (_??=_) as [E|E]; try (apply fin2nat_eq_iff in E; subst); try easy.
      destruct (_??=_) as [E1|E1]; try (apply fin2nat_eq_iff in E1; subst); try easy.
      destruct (_??=_) as [E2|E2]; try (apply fin2nat_eq_iff in E2; subst); try easy.
      rewrite eqnK_add. rewrite eqnAdd_assoc. auto.
    Qed.
    
  End eqnsAdd.


  (** ** 方程组的解 *)
  Section isAnswer.
    
    (** n元有序数组(c1,c2,...,cn)\T 是方程组 e 的一个“解” *)
    Definition isAnswer {n s} (e : Eqns n s) (c : @vec tA n) : Prop :=
      forall i, <fst (e.[i]), c> = snd (e.[i]).

    (** 若c是方程组e的一个解，则c也是 ([i],[j]) 后的方程组的解 *)
    Lemma isAnswer_eqnsSwap :
      forall {n s} (e : Eqns n s) (c : @vec tA n) (i j : fin s),
        isAnswer e c -> isAnswer (eqnsSwap e i j) c.
    Proof.
      intros. unfold isAnswer, eqnsSwap in *. intros k.
      unfold vswap. destruct (_??=_); auto. destruct (_??=_); auto.
    Qed.

    (** 若c是方程组e经过 ([i],[j]) 后的一个解，则c也是e的解 *)
    Lemma isAnswer_eqnsSwap_rev :
      forall {n s} (e : Eqns n s) (c : @vec tA n) (i j : fin s),
        isAnswer (eqnsSwap e i j) c -> isAnswer e c.
    Proof.
      intros.
      pose proof (isAnswer_eqnsSwap (eqnsSwap e i j) c j i H).
      rewrite eqnsSwap_eqnsSwap in H0. auto.
    Qed.
    
    (** 若c是方程组e的一个解，则c也是 [i] * K 后的方程组的解 *)
    Lemma isAnswer_eqnsScale :
      forall {n s} (e : Eqns n s) (c : @vec tA n) (i : fin s) (K : tA),
        isAnswer e c -> isAnswer (eqnsScale e i K) c.
    Proof.
      intros. unfold isAnswer, eqnsScale in *. intros k.
      destruct (_??=_); subst; simpl; auto. rewrite vdot_vscal_l.
      fin2nat; subst. specialize (H i); subst. rewrite <- H. auto.
    Qed.
    
    (** 若c是方程组e经过[i] * K 后的一个解，则c也是e的解 *)
    Lemma isAnswer_eqnsScale_rev :
      forall {n s} (e : Eqns n s) (c : @vec tA n) (i : fin s) (K : tA),
        K <> 0 -> isAnswer (eqnsScale e i K) c -> isAnswer e c.
    Proof.
      intros.
      pose proof (isAnswer_eqnsScale (eqnsScale e i K) c i (1/K) H0).
      rewrite eqnsScale_eqnsScale in H1.
      replace (K * (1/K)) with 1 in H1. rewrite eqnsScale_1 in H1. auto.
      field; auto.
    Qed.

    (** 若c是方程组e的一个解，则c也是 [j] + [i] * K 后的方程组的解 *)
    Lemma isAnswer_eqnsAdd :
      forall {n s} (e : Eqns n s) (c : @vec tA n) (i j : fin s) (K : tA),
        isAnswer e c -> isAnswer (eqnsAdd e i j K) c.
    Proof.
      intros. unfold isAnswer, eqnsAdd in *. intros k.
      destruct (_??=_); auto.
      unfold eqnAdd, eqnK; simpl. rewrite vdot_vadd_l.
      rewrite vdot_vscal_l. f_equal; auto. f_equal; auto.
    Qed.

    (** 若c是方程组e经过 [j] + [i] * K 后的一个解，则c也是e的解 *)
    Lemma isAnswer_eqnsAdd_rev :
      forall {n s} (e : Eqns n s) (c : @vec tA n) (i j : fin s) (K : tA),
        i <> j -> isAnswer (eqnsAdd e i j K) c -> isAnswer e c.
    Proof.
      intros. 
      pose proof (isAnswer_eqnsAdd (eqnsAdd e i j K) c i j (-K) H0).
      rewrite eqnsAdd_eqnsAdd in H1; auto.
      replace (K - K) with 0 in H1 by ring. rewrite eqnsAdd_K0 in H1; auto.
    Qed.
    
  End isAnswer.
  
  Section isAnswers.

    (* 方程组 e 的所有解组成的集合称为这个方程组的“解集” *)
    (* 从方程组的解集中，并且还符合实际问题需要的解时，称为“可行解” *)

    Definition isAnswers {n s t} (e : Eqns n s)
      (cs : @vec (@vec tA n) t) : Prop :=
      (forall c, isAnswer e c <-> lrep cs c).

    (* 若方程组有两个解集，则这两个解集等价 *)
    Lemma isAnswers_imply_equiv :
      forall {n s t1 t2} (e : Eqns n s)
        (cs1 : @vec (@vec tA n) t1) (cs2 : @vec (@vec tA n) t2),
        isAnswers e cs1 -> isAnswers e cs2 -> vsequiv cs1 cs2.
    Proof.
      intros. unfold isAnswers, vsequiv, lreps in *; split; intros.
      - pose proof (lrep_in cs2). unfold vforall in *; intros.
        rewrite <- H. rewrite H0. apply H1.
      - pose proof (lrep_in cs1). unfold vforall in *; intros.
        rewrite <- H0. rewrite H. apply H1.
    Qed.

    (* 若一个解集与方程组的解集等价，则这个新的解集也是方程组的解集 *)
    Lemma isAnswers_if_equiv :
      forall {n s t1 t2} (e : Eqns n s)
        (cs1 : @vec (@vec tA n) t1) (cs2 : @vec (@vec tA n) t2),
        isAnswers e cs1 -> vsequiv cs1 cs2 -> isAnswers e cs2.
    Proof.
      intros. destruct H0 as [HA HB]. hnf. 
      unfold isAnswers, vforall in *. split; intros.
      - rewrite H in H0. apply lreps_lrep with cs1; auto.
      - rewrite H. apply lreps_lrep with cs2; auto.
    Qed.
    
  End isAnswers.


  (** *** 同解 *)
  Section sameAnswers.

    (* 若方程组I与II的解集等价，则称I和II同解 *)
    Definition sameAnswers {n s1 s2 : nat} (e1 : Eqns n s1) (e2 : Eqns n s2) : Prop :=
      forall (t : nat) (cs : @vec (@vec tA n) t), isAnswers e1 cs <-> isAnswers e2 cs.

    Lemma sameAnswers_refl : forall {n s} (e : Eqns n s), sameAnswers e e.
    Proof. intros. hnf. tauto. Qed.

    Lemma sameAnswers_syms : forall {n s1 s2} (e1 : Eqns n s1) (e2 : Eqns n s2),
        sameAnswers e1 e2 -> sameAnswers e2 e1.
    Proof. intros. hnf in *. intros. split; intros; apply H; auto. Qed.
    
    Lemma sameAnswers_trans :
      forall {n s1 s2 s3} (e1 : Eqns n s1) (e2 : Eqns n s2) (e3 : Eqns n s3),
        sameAnswers e1 e2 -> sameAnswers e2 e3 -> sameAnswers e1 e3.
    Proof.
      intros. hnf in *. intros. split; intros.
      apply H0, H; auto. apply H, H0; auto.
    Qed.

    (* 方程组初等变换 ([i],[j]) 保持同解 *)
    Lemma sameAnswers_eqnsSwap : forall {n s} (e : Eqns n s) (i j : fin s),
        sameAnswers e (eqnsSwap e i j).
    Proof.
      intros. unfold sameAnswers, isAnswers; intros. split; split; intros.
      - apply H. apply isAnswer_eqnsSwap_rev in H0. auto.
      - apply isAnswer_eqnsSwap. apply H; auto.
      - apply H. apply isAnswer_eqnsSwap; auto.
      - rewrite <- H in H0. apply isAnswer_eqnsSwap_rev in H0; auto.
    Qed.  

    (* 方程组初等变换 [i] * K 保持同解 *)
    Lemma sameAnswers_eqnsScale : forall {n s} (e : Eqns n s) (i : fin s) (K : tA),
        K <> 0 -> sameAnswers e (eqnsScale e i K).
    Proof.
      intros. unfold sameAnswers, isAnswers; intros. split; intros ; split; intros.
      - apply H0. apply isAnswer_eqnsScale_rev in H1; auto.
      - apply isAnswer_eqnsScale. apply H0; auto.
      - apply H0. apply isAnswer_eqnsScale; auto.
      - apply H0 in H1. apply isAnswer_eqnsScale_rev in H1; auto.
    Qed.

    (* 方程组初等变换 [j] + [i] * K 保持同解 *)
    Lemma sameAnswers_eqnsAdd : forall {n s} (e : Eqns n s) (i j : fin s) (K : tA),
        i <> j -> sameAnswers e (eqnsAdd e i j K).
    Proof.
      intros. unfold sameAnswers, isAnswers; intros. split; intros; split; intros.
      - apply H0. apply isAnswer_eqnsAdd_rev in H1; auto.
      - apply isAnswer_eqnsAdd. apply H0; auto.
      - apply H0. apply isAnswer_eqnsAdd; auto.
      - apply H0 in H1. apply isAnswer_eqnsAdd_rev in H1; auto.
    Qed.

  End sameAnswers.

  
  (** *** 方程组的系数矩阵 *)
  Section coefMat.
        
    (* 取出s个方程的n元线性方程组的系数矩阵 *)
    Definition coefMat {n s} (e : Eqns n s) : mat s n := vmap fst e.


    Lemma coefMat_eqnsSwap :
      forall {n s} (e : Eqns n s) (i j : 'I_s),
      coefMat (eqnsSwap e i j) = mrowSwap i j (coefMat e).
    Proof.
      intros. unfold coefMat. apply meq_iff_mnth; intros a b.
      unfold mrowSwap, eqnsSwap, vswap. rewrite vnth_vmap.
      destruct (a ??= i); destruct (a ??= j); rewrite vnth_vmap; auto.
    Qed.

    Lemma coefMat_eqnsScale:
      forall {n s} (e : Eqns n s) (i : 'I_s) (K : tA),
      coefMat (eqnsScale e i K) = mrowScale i K (coefMat e).
    Proof.
      intros. unfold coefMat. apply meq_iff_mnth; intros a b.
      unfold mrowScale, eqnsScale, vswap. rewrite vnth_vmap.
      destruct (a ??= i); rewrite vnth_vmap; auto.
    Qed.

     Lemma coefMat_eqnsAdd:
      forall {n s} (e : Eqns n s) (i j: 'I_s) (K : tA),
      i <> j -> coefMat (eqnsAdd e i j K) = mrowAdd i j K (coefMat e).
    Proof.
      intros. unfold coefMat. apply meq_iff_mnth; intros a b.
      unfold mrowAdd, eqnsAdd, eqnAdd, vswap, vadd. rewrite vnth_vmap.
      destruct (a ??= i) as [E|E]; rewrite fin2nat_eq_iff in E; 
      rewrite vnth_vmap; subst; simpl fst; subst; auto.
    Qed.


  End coefMat.

  (** *** 方程组的系数矩阵 *)
  Section costMat.
        
    (* 取出s个方程的n元线性方程组的常数项 *)
    Definition costMat {n s} (e : Eqns n s) : vec s := vmap snd e.

    Lemma costMat_eqnsSwap :
      forall {n s} (e : Eqns n s) (i j : 'I_s),
      costMat (eqnsSwap e i j) = vswap (costMat e) i j .
    Proof.
      intros. unfold coefMat. apply veq_iff_vnth; intros a.
      unfold costMat, eqnsSwap, vswap. rewrite vnth_vmap.
      destruct (a ??= i); destruct (a ??= j); rewrite vnth_vmap; auto.
    Qed.

    
    (*
    
    Lemma costMat_eqnsScale:
      forall {n s} (e : Eqns n s) (i : 'I_s) (K : tA),
      costMat (eqnsScale e i K) = vscal K (costMat e) i   .
    Proof.
      intros. unfold coefMat. apply meq_iff_mnth; intros a b.
      unfold mrowScale, eqnsScale, vswap. rewrite vnth_vmap.
      destruct (a ??= i); rewrite vnth_vmap; auto.
    Qed.

     Lemma coefMat_eqnsAdd:
      forall {n s} (e : Eqns n s) (i j: 'I_s) (K : tA),
      i <> j -> coefMat (eqnsAdd e j i K) = mrowAdd i j K (coefMat e).
    Proof.
      intros. unfold coefMat. apply meq_iff_mnth; intros a b.
      unfold mrowAdd, eqnsAdd, eqnAdd, vswap, vadd. rewrite vnth_vmap.
      destruct (a ??= i) as [E|E]; rewrite fin2nat_eq_iff in E; 
      rewrite vnth_vmap; subst; simpl fst; subst; auto.
      rewrite vnth_vmap2; rewrite vnth_vmap. rewrite commutative.
      f_equal.
    Qed.
    *)

  End costMat.




  Lemma toEqns_eq : forall {n s : nat} (e : Eqns n s),
    e = toEqns (coefMat e) (costMat e).
  Proof.
    intros. apply veq_iff_vnth. intros; unfold toEqns.
    unfold coefMat. unfold costMat. induction s; fin.
    destruct (e i) as [v a] eqn : E. f_equal.
    - apply veq_iff_vnth. intros j. rewrite vnth_vmap.
      rewrite E. simpl; auto.
    - rewrite vnth_vmap. rewrite E. auto.
  Qed.

  Lemma vnth_toEqns : forall {n s : nat} (M : mat s n) (v : vec s) (i : 'I_s),
    (toEqns M v) i = (M.[i], v.[i]).
  Proof.
    intros. unfold toEqns. auto.
  Qed.

  Lemma toEqns_coefMat : forall {n s : nat} (M : mat s n) (v : vec s),
    coefMat (toEqns M v) = M.
  Proof.
    intros. unfold coefMat, toEqns. apply veq_iff_vnth; intros.
    rewrite vnth_vmap; auto.
  Qed.

  Lemma toEqns_costMat : forall {n s : nat} (M : mat s n) (v : vec s),
    costMat (toEqns M v) = v.
  Proof.
    intros. unfold costMat, toEqns. apply veq_iff_vnth; intros.
    rewrite vnth_vmap; auto.
  Qed.


    

  Section rowOps2eqn.

  Definition rowOps2eqn {n  s : nat} (l : list (@RowOp tA s)) (e : Eqns n (S s))
  : Eqns n (S s) :=
    fold_right (fun op e =>
      match op with
      | ROnop => e
      | ROswap i j => eqnsSwap e i j
      | ROscale i c => eqnsScale e i c
      | ROadd i j c => eqnsAdd e i j c
      end) e l.

  Lemma rowOps2eqn_app :
    forall {n s} (l1 l2 : list (@RowOp tA s)) (e : Eqns n (S s)),
  rowOps2eqn (l1 ++ l2) e = rowOps2eqn l1 (rowOps2eqn l2 e).
  Proof.
    intros n s l1. induction l1; intros.
    - simpl. auto.
    - replace ((a::l1)++l2)%list with (a:: (l1 ++ l2)) by auto.
      simpl. destruct a; try apply IHl1; try (f_equal; apply IHl1).
  Qed. 

  Lemma rowOps2eqn_eq : forall {n s} (l : list (@RowOp tA s)) (e : Eqns n (S s)),
    rowOps2eqn l e =
    toEqns (mmul (rowOps2mat l) (coefMat e))  (mmulv (rowOps2mat l) (costMat e)).
  Proof.
    intros n s l. induction l; intros.
    - simpl. rewrite mmul_1_l. rewrite mmulv_1_l. apply  toEqns_eq.
    - simpl rowOps2eqn. replace (a :: l) with ([a] ++ l)%list by auto.
      rewrite !rowOps2mat_app. simpl (rowOps2mat [a]). destruct a.
      + rewrite IHl. rewrite mmul_1_l. auto.
      + remember (rowOps2eqn l e) as e' eqn:Heq.
        rewrite  mmul_assoc. rewrite mmulv_assoc.
        rewrite IHl in Heq. 
        replace (mmul (rowOps2mat l) (coefMat e)) with (coefMat e').
        2 : { rewrite Heq. apply toEqns_coefMat. }
        replace (mmulv (rowOps2mat l) (costMat e)) with (costMat e').
        2 : { rewrite Heq. apply toEqns_costMat. }
        unfold eqnsSwap, toEqns, vswap. apply functional_extensionality; intros x.
        rewrite <- mrowSwap_mat1. rewrite mrowSwap_mat1_mmulv.
        unfold mrowSwap, vswap.
        destruct (x ??= i); destruct (x ??= j).
        replace (e' j) with ((toEqns (coefMat e') (costMat e')) j).
        2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
        replace (e' j) with ((toEqns (coefMat e') (costMat e')) j).
        2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
        replace (e' j) with ((toEqns (coefMat e') (costMat e')) j).
        2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
        replace (e' i) with ((toEqns (coefMat e') (costMat e')) i).
        2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
        replace (e' x) with ((toEqns (coefMat e') (costMat e')) x).
        2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
      + remember (rowOps2eqn l e) as e' eqn:Heq.
        rewrite  mmul_assoc. rewrite mmulv_assoc.
        rewrite IHl in Heq. 
        replace (mmul (rowOps2mat l) (coefMat e)) with (coefMat e').
        2 : { rewrite Heq. apply toEqns_coefMat. }
        replace (mmulv (rowOps2mat l) (costMat e)) with (costMat e').
        2 : { rewrite Heq. apply toEqns_costMat. }
        unfold eqnsScale, toEqns, vswap. apply functional_extensionality; intros x.
        rewrite <- mrowScale_mat1. rewrite mrowScale_mat1_mmulv.
        unfold mrowScale. destruct (x ??= i); f_equal.
        replace (e' x) with ((toEqns (coefMat e') (costMat e')) x).
        2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
      + remember (rowOps2eqn l e) as e' eqn:Heq.
        rewrite  mmul_assoc. rewrite mmulv_assoc.
        rewrite IHl in Heq. 
        replace (mmul (rowOps2mat l) (coefMat e)) with (coefMat e').
        2 : { rewrite Heq. apply toEqns_coefMat. }
        replace (mmulv (rowOps2mat l) (costMat e)) with (costMat e').
        2 : { rewrite Heq. apply toEqns_costMat. }
        rewrite <- mrowAdd_mat1. rewrite mrowAdd_mat1_mmulv.
        unfold eqnsAdd, eqnAdd, eqnK, toEqns. 
        apply functional_extensionality; intros x.
        unfold mrowAdd, eqnAdd, eqnK. 
        destruct (x ??= i); destruct (x ??= j);
        try (rewrite fin2nat_eq_iff in e0; subst i);
        try (rewrite fin2nat_eq_iff in e1; subst j); simpl; try f_equal.
        * replace (e' x) with ((toEqns (coefMat e') (costMat e')) x).
          2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
        * replace (e' x) with ((toEqns (coefMat e') (costMat e')) x).
          2 : { rewrite <- toEqns_eq. auto. } unfold toEqns. f_equal.
  Qed.

End rowOps2eqn.

  Section rowOpsinV.

  Definition rowOpsInV { s : nat} (l : list (@RowOp tA s)) (V: vec (S s))
  : vec (S s) :=
    fold_right (fun op e =>
      match op with
      | ROnop => e
      | ROswap i j => vswap e i j
      | ROscale i c => fun j : 'I_(S s) => if j ??= i then (Amul c e.[j]) else e.[j]
      | ROadd i j c => fun x : 'I_(S s) => if x ??= i then (Aadd e.[x] (Amul c e.[j])) else e.[x]
      end) V l.

  

  Lemma rowOpsInV_app :
    forall { s} (l1 l2 : list (@RowOp tA s)) (V: vec (S s)),
    rowOpsInV (l1 ++ l2) V = rowOpsInV l1 (rowOpsInV l2 V).
  Proof.
    intros s l1. induction l1; intros.
    - simpl. auto.
    - replace ((a::l1)++l2)%list with (a:: (l1 ++ l2)) by auto.
      simpl. destruct a; try apply IHl1.
      + f_equal; apply IHl1.
      + apply functional_extensionality. intros.
        destruct (x ??= i). f_equal. rewrite IHl1. auto.
        rewrite IHl1; auto.
      + apply functional_extensionality. intros.
        destruct (x ??= i). rewrite IHl1. auto. rewrite IHl1. auto.
  Qed.

  Lemma rowOpsInV_eq :
    forall {s} (l: list (@RowOp tA s)) (V: vec (S s)),
    rowOpsInV l V = mmulv (rowOps2mat l) V.
  Proof.
    intros s l. induction l; intros.
    - simpl. rewrite mmulv_1_l. auto.
    - simpl. destruct a; auto.
      + rewrite IHl. apply v2cv_inj. rewrite v2cv_mmulv.
        rewrite <- mrowSwap_mmul. apply cv2v_inj.
        rewrite cv2v_v2cv. apply veq_iff_vnth; intros x.
        unfold cv2v. unfold vswap, mrowSwap.
        destruct (x ??= i) as [E|E].
        * rewrite <- v2cv_mmulv. apply v2cv_spec.
        * destruct  (x ??= j) as [E'|E']; rewrite <- v2cv_mmulv; apply v2cv_spec.
      + rewrite IHl. apply v2cv_inj. rewrite v2cv_mmulv.
        rewrite <- mrowScale_mmul. apply cv2v_inj.
        rewrite cv2v_v2cv. apply veq_iff_vnth; intros x.
        unfold cv2v. unfold mrowScale.
        destruct (x ??= i) as [E|E]; f_equal. rewrite <- v2cv_mmulv. apply v2cv_spec.
      + rewrite IHl. apply v2cv_inj. rewrite v2cv_mmulv.
        rewrite <- mrowAdd_mmul. apply cv2v_inj.
        rewrite cv2v_v2cv. apply veq_iff_vnth; intros x.
        unfold cv2v. unfold mrowAdd.
        destruct (x ??= i) as [E|E]; f_equal. rewrite <- v2cv_mmulv. apply v2cv_spec.
  Qed.


  End rowOpsinV.

  (** *** 方程组的增广矩阵 *)
  Section extMat.
    
    (* 将s个方程的n元线性方程组转换为s行(n+1)列的增广矩阵 *)
    Definition eqns2extMat {n s} (e : Eqns n s) : mat s (S n) :=
      mconscT (vmap fst e) (vmap snd e).

    (* 将s行(n+1)列的增广矩阵转换为s个方程的n元线性方程组 *)
    Definition extMat2eqns {n s : nat} (e : mat s (S n)) : Eqns n s :=
      fun i => (vremoveT (e.[i]), vtail e.[i]).

    Lemma eqns2extMat_extMat2eqns : forall {n s} (e : mat s (S n)),
        eqns2extMat (extMat2eqns e) = e.
    Proof.
      intros. unfold eqns2extMat, extMat2eqns. apply meq_iff_mnth; intros i j.
      destruct (j ??= n); subst; simpl.
      - rewrite mnth_mconscT_n; auto. rewrite vnth_vmap. simpl.
        rewrite vtail_eq; f_equal; fin.
      - rewrite mnth_mconscT_lt with (H:=fin2nat_neq_n_imply_lt n j n0).
        rewrite vnth_vmap. simpl. rewrite vnth_vremoveT.
        rewrite fSuccRange_fPredRange. auto.
    Qed.

    Lemma extMat2eqns_eqns2extMat : forall {n s} (e : Eqns n s),
        extMat2eqns (eqns2extMat e) = e.
    Proof.
      intros. unfold eqns2extMat, extMat2eqns. apply veq_iff_vnth; intros i.
      rewrite vnth_mconscT. rewrite vremoveT_vconsT, vtail_vconsT.
      rewrite !vnth_vmap. rewrite <- surjective_pairing; auto.
    Qed.
    
  End extMat.

  (** *** 矩阵的初等行变换 *)
  Section MRT.
    (* MRT: Matrix Row Transformn *)
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
        (exists (l : list (@RowOp tA r)), Forall roValid l /\ mmul (rowOps2mat l) M = N).
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




  End MRT.


    (** ** 方程组的初等变换 *)
  Section EqnsTrans.
    
    (** 方程组的初等变换 *)
    Inductive EqnsTrans {n s} : Eqns n s -> Eqns n s -> Prop :=
    | ETswap (i j : fin s) : forall e : Eqns n s, EqnsTrans e (eqnsSwap e i j)
    | ETscale (i : fin s) (K : tA) : forall e : Eqns n s,
        K <> 0 -> EqnsTrans e (eqnsScale e i K)
    | ETadd (i j : fin s) (K : tA) : forall e : Eqns n s,
        i <> j -> EqnsTrans e (eqnsAdd e i j K)
    | ETtrans : forall e1 e2 e3 : Eqns n s,
        EqnsTrans e1 e2 -> EqnsTrans e2 e3 -> EqnsTrans e1 e3
    | ETrefl : forall e : Eqns n s, EqnsTrans e e.

    (* 方程组的初等变换保持同解 *)
    Lemma sameAnswers_eqnsTrans : forall {n s} (e1 e2 : Eqns n s),
        EqnsTrans e1 e2 -> sameAnswers e1 e2.
    Proof.
      intros. induction H as [i j H|i K H|i j K H|e1 e2 e3 H1 H2|e].
      - apply sameAnswers_eqnsSwap.
      - apply sameAnswers_eqnsScale; auto.
      - apply sameAnswers_eqnsAdd; auto.
      - apply sameAnswers_trans with e2; auto.
      - apply sameAnswers_refl. 
    Qed.

    Lemma MRT_eqnsTrans : forall {n s} (e : Eqns n s) (N : mat s n),
      MRT (coefMat e) N -> exists e', EqnsTrans e e' /\ (coefMat e') = N.
    Proof.
      intros. remember (coefMat e) as M eqn:Heq.
      generalize dependent e. induction H; intros.
      - exists (eqnsSwap e i j); split. apply ETswap. rewrite Heq.
        apply coefMat_eqnsSwap.
      - exists (eqnsScale e i K); split. apply ETscale; auto.
        rewrite Heq. apply coefMat_eqnsScale.
      - exists (eqnsAdd e i j K); split. apply ETadd; auto.
        rewrite Heq. apply coefMat_eqnsAdd; auto.
      - exists e. split. apply ETrefl. symmetry; auto.
      - apply IHMRT1 in Heq. clear IHMRT1. destruct Heq as [e' [H1 H2]].
        symmetry in H2. apply IHMRT2 in H2; clear IHMRT2.
        destruct H2 as [e'' [H2 H3]]. exists e''. split.
        apply ETtrans with e'; auto. auto.
    Qed.

  End EqnsTrans.
  (** ** 阶梯形矩阵 *)
  
 (*

(** 求解 其次线性方程组*)
  Program Fixpoint solveAnswers_aux {n s} (A : mat (S n) (S s))  (l : list (@vec tA (S s))) 
    (x y : nat) {measure (x + y)} : list (vec (S s)) :=
    match x, y with
    | O, _ => l
    | _, O => l
    | S x', S y' => 
      match @getrowPivot  A (S s) #x' with
      | None => solveAnswers_aux A l x' y
      | Some a =>
      if a ??= y'
        then solveAnswers_aux A l x' y'
        else solveAnswers_aux A ((l2v (v2l (vopp (mcol A #y')))) :: l) x y'
      end
    end.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Definition solveAnswers {n s} (e : Eqns (S n) (S s)) :=
  solveAnswers_aux (coefMat e) nil (S n) (S s).
*)
  End SystemOfLinearEquations.
