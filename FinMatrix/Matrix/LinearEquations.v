Require Export VectorSpace.

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
  Notation l2v := (@l2v _ vzero).
  Notation vopp := (@vopp _ Aopp).
  Notation vscale := (@vscale _ Amul).
  Notation vadde := (@vadde _ Aadd Amul).
  Notation vsum := (@vsum _ vadd vzero _).
  
  Notation mat r c := (mat tA r c).
  Notation mat1  := (@mat1 tA Azero Aone).
  Notation mrowSwap := (@mrowSwap tA).
  Notation mrowScale := (@mrowScale _ Amul).
  Notation mrowAdd := (@mrowAdd _ Aadd Amul).
  Notation mmul := (@mmul tA Aadd 0 Amul).
  Notation mmulv := (@mmulv tA Aadd 0 Amul).
  Infix "*" := mmul : mat_scope.
  Infix "*v" := mmulv : mat_scope.

  Notation lrep := (@lrep _ _ vadd vzero vscal).
  Notation lreps := (@lreps _ _ vadd vzero vscal).
  Notation ldep := (@ldep _ Azero _ vadd vzero vscal).
  Notation lindep := (@lindep _ Azero _ vadd vzero vscal).
  Notation lcomb := (@lcomb tA _ vadd vzero  vscal).

  Notation rowOps2mat := (@rowOps2mat tA Aadd Azero Amul Aone).
  Notation rowOps2matInv := (@rowOps2matInv _ Aadd 0 Aopp Amul 1 Ainv).
  Notation roValid := (@roValid tA Azero).
  Notation MRT := (@MRT _ Aadd Azero Amul).

  Notation isREF := (@isREF _ 0 _).
  Notation isRREF := (@isRREF _ 0 1 _).
  Notation toREF := (@toREF _ Aadd 0 Aopp Amul Ainv _).
  Notation REF2RREF := (@REF2RREF _ Aadd 0 Aopp Amul _).
  Notation toRREF := (@toRREF _ Aadd 0 Aopp Amul Ainv _).
  Notation toRREF' := (@toRREF' _ Aadd 0 Aopp Amul Ainv _).
  Notation ElimDown := (@ElimDown _ Aadd 0 Aopp Amul _).

  Notation getrowPivot := (getrowPivot (Azero:=0)).
  Notation getcolPivot := (getcolPivot (Azero:=0)).
  Notation sm2REF := (@sm2REF _ Aadd 0 Aopp Amul Ainv _).
  Notation sm2RREF := (@sm2RREF _ Aadd 0 Aopp Amul _).

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

  Definition eqnsSwap {n s} (e : Eqns n s) (i j : 'I_s) : Eqns n s := 
    (vmap (fun v => vswap v i j) (fst e), vswap (snd e) i j).

  Lemma eqnsSwap_eqnsSwap : forall {n s} (e : Eqns n s) (i j : fin s),
    eqnsSwap (eqnsSwap e i j) j i = e.
  Proof. 
    intros. unfold eqnsSwap. destruct e as [A B]. simpl.
    f_equal. 2:{ apply vswap_vswap. } apply meq_iff_mnth.
    intros a b. repeat rewrite vnth_vmap. rewrite vswap_vswap.
    auto.
  Qed.

  (** *** 方程组初等变换之某行乘以非零常数 *)
    
    (* 方程组第i行乘以K，记作 [i] * K。注：要求k非零 *)
  Definition eqnsScale {n s} (e : Eqns n s) (i : fin s) (K : tA) : Eqns n s :=
      (vmap (fun v => vscale v i K) (fst e), vscale (snd e) i K).

  Lemma eqnsScale_1 : forall {n s} (e : Eqns n s) (i : fin s), eqnsScale e i 1 = e.
  Proof.
    intros. destruct e as [A B]. unfold eqnsScale; simpl. f_equal.
    - apply veq_iff_vnth; intros a. rewrite vnth_vmap.
      apply veq_iff_vnth; intros b. unfold vscale.
      destruct (b ??= i) as [E|E]; fin. replace (1 * A a i)%A with (A a i) by fin.
      f_equal. fin.
    - apply veq_iff_vnth; intros a. unfold vscale. 
      destruct (a ??= i) as [E|E]; fin. replace (1 * B i)%A with (B i)%A by fin.
      f_equal. fin.
  Qed.

  Lemma eqnsScale_eqnsScale : forall {n s} (e : Eqns n s) (i : fin s) (K1 K2 : tA),
    eqnsScale (eqnsScale e i K1) i K2 = eqnsScale e i (K1*K2)%A.
  Proof.
    intros. unfold eqnsScale. destruct e as [A B]. simpl. f_equal.
    - apply meq_iff_mnth. intros a b. rewrite !vnth_vmap.
      unfold vscale. destruct (b ??= i); destruct (i ??= i); fin.
    - unfold vscale. extensionality j.
      destruct (j ??= i); destruct (i ??= i); fin.
  Qed.

  (* 方程组第i行乘以K加到第j行，记作 [i] + [j] * K。注：要求i和j不同 *)
  Definition eqnsAdd {n s} (e : Eqns n s) (i j : fin s) (K : tA) : Eqns n s :=
    (vmap (fun v => vadde v i j K) (fst e), vadde (snd e) i j K).

  Lemma eqnsAdd_K0 : forall {n s} (e : Eqns n s) (i j : fin s), eqnsAdd e i j 0 = e.
  Proof.
    intros. destruct e as [A B]. unfold eqnsAdd; simpl. f_equal.
    - apply veq_iff_vnth; intros p. rewrite vnth_vmap.
      apply veq_iff_vnth; intros q. unfold vadde.
      destruct (q ??= i) as [E|E]; fin.
      replace (A p i + 0 * A p j)%A with (A p i)%A by fin. f_equal; fin.
    - apply veq_iff_vnth; intros p. unfold vadde.
      destruct (p ??= i) as [E|E]; fin. 
      replace (B i + 0 * B j)%A with (B i)%A by fin. f_equal; fin.
  Qed.

  Lemma eqnsAdd_eqnsAdd : forall {n s} (e : Eqns n s) (i j : 'I_s) (K1 K2 : tA),
    i <> j -> eqnsAdd (eqnsAdd e i j K1) i j K2 = eqnsAdd e i j (K1+K2)%A.
  Proof.
    intros. unfold eqnsAdd. destruct e as [A B]. simpl. f_equal.
    - apply meq_iff_mnth. intros a b. rewrite !vnth_vmap.
      unfold vadde. destruct (b ??= i); destruct (i ??= i); destruct (j ??= i); fin.
    - unfold vadde. extensionality k.
      destruct (k ??= i); destruct (i ??= i); destruct (j ??= i); fin.
  Qed.

 

 
  (** *** 方程组的系数矩阵 *)
    (* 取出s个方程的n元线性方程组的系数矩阵 *)
  Definition coefMat {n s} (e : Eqns n s) : mat s n := mtrans (fst e).

  Lemma coefMat_eqnsSwap :
    forall {n s} (e : Eqns n s) (i j : 'I_s),
    coefMat (eqnsSwap e i j) = mrowSwap i j (coefMat e).
  Proof.
    intros. unfold coefMat. destruct e as [A B]. simpl.
    apply meq_iff_mnth; intros a b. unfold mtrans. rewrite vnth_vmap.
    unfold mrowSwap, eqnsSwap, vswap. auto. 
  Qed.

  Lemma coefMat_eqnsScale:
    forall {n s} (e : Eqns n s) (i : 'I_s) (K : tA),
    coefMat (eqnsScale e i K) = mrowScale i K (coefMat e).
  Proof.
    intros. unfold coefMat. destruct e as [A B]. simpl.
    apply meq_iff_mnth; intros a b. unfold mtrans. rewrite vnth_vmap.
    unfold mrowScale, eqnsScale, vscale. destruct (a ??= i); fin.
  Qed.

  Lemma coefMat_eqnsAdd:
    forall {n s} (e : Eqns n s) (i j: 'I_s) (K : tA),
    i <> j -> coefMat (eqnsAdd e i j K) = mrowAdd i j K (coefMat e).
  Proof.
    intros. unfold coefMat. destruct e as [A B]. simpl.
    apply meq_iff_mnth; intros a b. unfold mtrans. rewrite vnth_vmap.
    unfold mrowAdd, eqnsAdd, eqnAdd, vswap, vadde. destruct (a ??= i); fin.
    repeat f_equal; fin.
  Qed.

        
    (* 取出s个方程的n元线性方程组的常数项 *)
  Definition costMat {n s} (e : Eqns n s) : vec s := snd e.

  Lemma costMat_eqnsSwap :
    forall {n s} (e : Eqns n s) (i j : 'I_s),
    costMat (eqnsSwap e i j) = vswap (costMat e) i j .
  Proof.
    intros. unfold costMat. destruct e as [A B]. simpl. auto. 
  Qed.

  Lemma costMat_eqnsScale:
    forall {n s} (e : Eqns n s) (i : 'I_s) (K : tA),
    costMat (eqnsScale e i K) = vscale (costMat e) i K.
  Proof.
    intros. unfold costMat. destruct e as [A B]. simpl. auto. 
  Qed.

  Lemma costMat_eqnsAdd:
    forall {n s} (e : Eqns n s) (i j: 'I_s) (K : tA),
    costMat (eqnsAdd e i j K) = vadde (costMat e) i j K.
  Proof.
    intros. unfold costMat. destruct e as [A B]. simpl. auto.
  Qed. 


  Definition toEqns {s n} (A : mat s n) (B: vec s) : Eqns n s :=
    (mtrans A, B).

  Lemma toEqns_eq : forall {n s : nat} (e : Eqns n s),
    e = toEqns (coefMat e) (costMat e).
  Proof.
    intros. destruct e as [A B]. unfold coefMat. simpl.
    unfold toEqns; f_equal.
  Qed.


  Lemma toEqns_coefMat : forall {n s : nat} (M : mat s n) (v : vec s),
    coefMat (toEqns M v) = M.
  Proof.
    intros. unfold coefMat, toEqns. simpl. apply mtrans_mtrans.
  Qed.

  Lemma toEqns_costMat : forall {n s : nat} (M : mat s n) (v : vec s),
    costMat (toEqns M v) = v.
  Proof.
    intros. unfold costMat, toEqns. auto.
  Qed.

   (** n元有序数组(c1,c2,...,cn)\T 是方程组 e 的一个“解” *)
  Definition isAnswer {n s} (e : Eqns n s) (c : @vec tA n) : Prop :=
    c <> vzero /\ lcomb c (fst e) = snd e.

    (** 若c是方程组e的一个解，则c也是 ([i],[j]) 后的方程组的解 *)
  Lemma isAnswer_eqnsSwap :
    forall {n s} (e : Eqns n s) (c : @vec tA n) (i j : fin s),
      isAnswer e c -> isAnswer (eqnsSwap e i j) c.
  Proof.
    intros. destruct e as [A B].
    unfold isAnswer, eqnsSwap in *. simpl in *. destruct H. split; auto.
    apply veq_iff_vnth. intros p. rewrite <- H0.
    unfold lcomb. rewrite vsum_vswap. f_equal.
    apply veq_iff_vnth. intros a. rewrite vnth_vmap2.
    rewrite !vnth_vmap. rewrite vnth_vmap2.
    apply veq_iff_vnth. intros q. rewrite vnth_vscal.
    unfold vswap; destruct (q ??= i) as [E|E]; destruct (q ??= j) as [E'|E'];
    rewrite vnth_vscal; fin.
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
    intros. destruct e as [A B].
    unfold isAnswer, eqnsSwap in *. simpl in *. destruct H. split; auto.
    apply veq_iff_vnth. intros p. rewrite <- H0.
    unfold lcomb. rewrite vsum_vscale. f_equal.
    apply veq_iff_vnth. intros a. rewrite vnth_vmap2.
    rewrite !vnth_vmap. rewrite vnth_vmap2.
    apply veq_iff_vnth. intros q. rewrite vnth_vscal.
    unfold vscale. destruct (q ??= i) as [E|E];
    rewrite vnth_vscal; fin.
  Qed.
    
    (** 若c是方程组e经过[i] * K 后的一个解，则c也是e的解 *)
  Lemma isAnswer_eqnsScale_rev :
    forall {n s} (e : Eqns n s) (c : @vec tA n) (i : fin s) (K : tA),
      K <> 0 -> isAnswer (eqnsScale e i K) c -> isAnswer e c.
  Proof.
    intros.
    pose proof (isAnswer_eqnsScale (eqnsScale e i K) c i (1/K) H0).
    rewrite eqnsScale_eqnsScale in H1.
    replace (K * (1/K))%A with 1 in H1. 
    rewrite eqnsScale_1 in H1. auto. field. auto.
  Qed.

    (** 若c是方程组e的一个解，则c也是 [j] + [i] * K 后的方程组的解 *)
  Lemma isAnswer_eqnsAdd :
    forall {n s} (e : Eqns n s) (c : @vec tA n) (i j : fin s) (K : tA),
      isAnswer e c -> isAnswer (eqnsAdd e i j K) c.
  Proof.
    intros. destruct e as [A B].
    unfold isAnswer, eqnsAdd in *. simpl in *. destruct H. split; auto.
    apply veq_iff_vnth. intros p. rewrite <- H0.
    unfold lcomb. rewrite vsum_vadde. f_equal.
    apply veq_iff_vnth. intros a. rewrite vnth_vmap2.
    rewrite !vnth_vmap. rewrite vnth_vmap2.
    apply veq_iff_vnth. intros q. rewrite !vnth_vscal.
    unfold vadde. destruct (q ??= i) as [E|E];
    rewrite !vnth_vscal; fin.
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

    Lemma isAnswer_eq : 
    forall {n s} (e : Eqns n s) (c : @vec tA n),
    isAnswer e c <-> c <> vzero /\ coefMat e *v c = costMat e.
  Proof.
    intros. destruct e as [A B].  
    unfold isAnswer, coefMat, costMat; simpl; split; intros.
    - destruct H. split; auto. rewrite <- H0. unfold lcomb, mmulv, mtrans, vdot.
      apply veq_iff_vnth. intros i.
      rewrite vnth_vsum. f_equal. apply veq_iff_vnth; intros j.
      rewrite !vnth_vmap2. rewrite vnth_vscal. fin.
    - destruct H. split; auto. rewrite <- H0.  unfold lcomb, mmulv, mtrans, vdot.
      apply veq_iff_vnth. intros i.
      rewrite vnth_vsum. f_equal. apply veq_iff_vnth; intros j.
      rewrite !vnth_vmap2. rewrite vnth_vscal. fin.
  Qed.

  Definition Answers (n : nat) : Type := (list (@vec tA n)) * (@vec tA n). 

  Definition inAnswers {n : nat} (ans : Answers n) (c : @vec tA n) :=
  exists (cs : list tA), (fold_right vadd vzero (map2 vscal cs (fst ans))) + (snd ans) = c.

  Definition ansequiv {n : nat} (ans1 : Answers n) (ans2 : Answers n) :=
    forall c, inAnswers ans1 c <-> inAnswers ans2 c.
  
  (* 方程组 e 的所有解组成的集合称为这个方程组的“解集” *)
  (* 从方程组的解集中，并且还符合实际问题需要的解时，称为“可行解” *)
  Definition isAnswers {n s} (e : Eqns n s) (ans : Answers n) : Prop :=
    forall c, isAnswer e c <-> inAnswers ans c.

  
    (* 若方程组有两个解集，则这两个解集等价 *)
  Axiom isAnswers_imply_equiv :
    forall {n s} (e : Eqns n s)
      (ans1 ans2: Answers n),
      isAnswers e ans1 -> isAnswers e ans2 -> ansequiv ans1 ans2.


    (* 若一个解集与方程组的解集等价，则这个新的解集也是方程组的解集 *)
  Axiom isAnswers_if_equiv :
    forall {n s} (e : Eqns n s)
      (ans1 ans2: Answers n) c,
      inAnswers ans1 c -> ansequiv ans1 ans2 -> inAnswers ans2 c.

    (* 若方程组I与II的解集等价，则称I和II同解 *)
  Definition sameAnswers {n s1 s2 : nat} (e1 : Eqns n s1) (e2 : Eqns n s2) : Prop :=
    forall (t : nat) (ans : Answers n), isAnswers e1 ans <-> isAnswers e2 ans.

  Axiom sameAnswers_refl : forall {n s} (e : Eqns n s), sameAnswers e e.

  Axiom sameAnswers_syms : forall {n s1 s2} (e1 : Eqns n s1) (e2 : Eqns n s2),
    sameAnswers e1 e2 -> sameAnswers e2 e1.
    
  Axiom sameAnswers_trans :
    forall {n s1 s2 s3} (e1 : Eqns n s1) (e2 : Eqns n s2) (e3 : Eqns n s3),
      sameAnswers e1 e2 -> sameAnswers e2 e3 -> sameAnswers e1 e3.

    (* 方程组初等变换 ([i],[j]) 保持同解 *)
  Axiom sameAnswers_eqnsSwap : forall {n s} (e : Eqns n s) (i j : fin s),
    sameAnswers e (eqnsSwap e i j).

    (* 方程组初等变换 [i] * K 保持同解 *)
  Axiom sameAnswers_eqnsScale : forall {n s} (e : Eqns n s) (i : fin s) (K : tA),
    K <> 0 -> sameAnswers e (eqnsScale e i K).

    (* 方程组初等变换 [j] + [i] * K 保持同解 *)
  Axiom sameAnswers_eqnsAdd : forall {n s} (e : Eqns n s) (i j : fin s) (K : tA),
      i <> j -> sameAnswers e (eqnsAdd e i j K).

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
        unfold eqnsSwap, toEqns, vswap. f_equal.
        * extensionality x. rewrite <- mrowSwap_mat1. rewrite vnth_vmap.
          extensionality y. unfold mtrans. unfold mrowSwap, coefMat, mtrans.
          destruct (x ??= i); destruct (x ??= j); fin.
        * rewrite mrowSwap_mat1_mmulv. extensionality x.
          unfold vswap. unfold costMat. auto.
      + remember (rowOps2eqn l e) as e' eqn:Heq.
        rewrite  mmul_assoc. rewrite mmulv_assoc.
        rewrite IHl in Heq. 
        replace (mmul (rowOps2mat l) (coefMat e)) with (coefMat e').
        2 : { rewrite Heq. apply toEqns_coefMat. }
        replace (mmulv (rowOps2mat l) (costMat e)) with (costMat e').
        2 : { rewrite Heq. apply toEqns_costMat. }
        unfold eqnsScale, toEqns, vswap. f_equal.
        * extensionality x. rewrite <- mrowScale_mat1. rewrite vnth_vmap.
          extensionality y. unfold mtrans. unfold mrowScale, coefMat, mtrans, vscale.
          destruct (y ??= i); fin.
        * rewrite mrowScale_mat1_mmulv. extensionality x.
          unfold vscale. unfold costMat. destruct (x ??= i); fin.
      + remember (rowOps2eqn l e) as e' eqn:Heq.
        rewrite  mmul_assoc. rewrite mmulv_assoc.
        rewrite IHl in Heq. 
        replace (mmul (rowOps2mat l) (coefMat e)) with (coefMat e').
        2 : { rewrite Heq. apply toEqns_coefMat. }
        replace (mmulv (rowOps2mat l) (costMat e)) with (costMat e').
        2 : { rewrite Heq. apply toEqns_costMat. }
        rewrite <- mrowAdd_mat1. rewrite mrowAdd_mat1_mmulv.
        unfold eqnsAdd, eqnAdd, eqnK, toEqns. f_equal. 
        * extensionality x. rewrite vnth_vmap.
          extensionality y. unfold mtrans. unfold mrowAdd, coefMat, mtrans, vadde.
          destruct (y ??= i); fin. repeat f_equal; fin.
        * extensionality x. unfold vadde. unfold costMat.
          destruct (x ??= i); fin. repeat f_equal; fin.
  Qed.

  Definition rowOpsInV {s : nat} (l : list (@RowOp tA s)) (V: vec (S s))
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

    (* 将s个方程的n元线性方程组转换为s行(n+1)列的增广矩阵 *)
  Definition eqns2extMat {n s} (e : Eqns n s) : mat s (S n) :=
    mconscT (coefMat e) (costMat e).

  (* 将s行(n+1)列的增广矩阵转换为s个方程的n元线性方程组 *)
  Definition extMat2eqns {n s : nat} (e : mat s (S n)) : Eqns n s :=
    toEqns (mremovecT e) (mtailc e).

  Lemma eqns2extMat_extMat2eqns : forall {n s} (e : mat s (S n)),
      eqns2extMat (extMat2eqns e) = e.
  Proof.
    intros. unfold eqns2extMat, extMat2eqns. apply meq_iff_mnth; intros i j.
    unfold mconscT. rewrite vnth_vmap2. unfold toEqns.
    unfold costMat, coefMat; simpl. rewrite mtrans_mtrans.
    unfold vconsT. destruct (j ??< n) as [E|E].
    - unfold mremovecT. rewrite vnth_vmap. rewrite vnth_vremoveT. 
      f_equal; fin.
    - unfold mtailc, vtail. f_equal. pose proof (fin2nat_lt j).
      assert (fin2nat j = n) by lia. fin.
  Qed. 
         
  Lemma extMat2eqns_eqns2extMat : forall {n s} (e : Eqns n s),
    extMat2eqns (eqns2extMat e) = e.
  Proof.
    intros. unfold eqns2extMat, extMat2eqns. 
    destruct e as [A B].
    unfold toEqns, coefMat, costMat. simpl. f_equal.
    - apply meq_iff_mnth. intros i j. unfold mtrans, mremovecT, mconscT.
      rewrite vnth_vmap. rewrite vnth_vremoveT.
      rewrite vnth_vmap2. unfold vconsT. destruct (fSuccRange i ??< n) as [E|E].
      + f_equal; fin.
      + exfalso. apply E. pose proof (fin2nat_lt i); fin.
    - apply veq_iff_vnth. intros i. unfold mtailc, vtail.
      unfold mconscT. rewrite vnth_vmap2. unfold vconsT.
      destruct (#n ??< n) as [E|E]; fin.
      exfalso. rewrite fin2nat_nat2finS in E; fin.
  Qed. 
  
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
  Check fold_left.

  Definition isRREFSolve_helper {r c} (V : @vec 'I_(S c) (S r)) (v : @vec tA (S r)) (x y : nat): @vec tA (S c) :=
    vset (fold_left
    (fun v' i => vset v' V.[#i] (- v.[#i]))
    (seq 0 x) vzero) #y Aone.


  Fixpoint isRREFSolve {r c} (M : mat  (S r) (S c)) (b : @vec tA (S r)) (V : @vec 'I_(S c) (S r))(x y : nat) (ans : Answers (S c)) : Answers (S c) :=
  match x, y with
  | O, _ => ans
  | _, O => ans
  | S x', S y' => 
    let a := V.[#x'] in
    if (fin2nat a ??= y') 
      then isRREFSolve M b V x' y' (fst ans, fun i : 'I_(S c)=> if i ??= x' then b.[#x']%A else (snd ans).[i])
      else isRREFSolve M b V x y' (cons (isRREFSolve_helper V M&[#y'] x y') (fst ans), snd ans)
  end.


  Fixpoint hasAnswers_aux {r} (b : @vec tA (S r)) (x : nat) : bool :=
    match x with
    | O => true
    | S x' =>
      if Aeqdec (b.[#(r - x')]) Azero then hasAnswers_aux b x'
      else false
    end.

  Definition hasAnswers {r} (b : @vec tA (S r)) (x : nat) : bool :=
    hasAnswers_aux b (S r - x).


  Definition SolveMatrix {r c} (M : mat (S r) (S c)) (b : @vec tA (S r)): (Answers (S c)) :=
    let '(l, N, num, V) := toRREF' M in
    let b' := rowOpsInV l b in
    if hasAnswers b' num then (isRREFSolve N b' V num (S c) (nil, vzero)) else (nil, vzero).

  Definition SolveEqns {n s} (E : Eqns (S n) (S s)) :(Answers (S n)) :=
    SolveMatrix (coefMat E) (costMat E).

(*
  Lemma isBasicAnswers_imply_equiv :
    forall {n s t1 t2} (e : Eqns n s)
      (cs1 : @vec (@vec tA n) t1) (cs2 : @vec (@vec tA n) t2),
      isBasicAnswers e cs1 -> isBasicAnswers e cs2 -> vsequiv cs1 cs2 /\ t1 = t2.
  Proof.
    intros. unfold isAnswers, vsequiv, lreps in *; split; intros.
    - pose proof (lrep_in cs2). unfold vforall in *; intros.
      rewrite <- H. rewrite H0. apply H1.
    - pose proof (lrep_in cs1). unfold vforall in *; intros.
      rewrite <- H0. rewrite H. apply H1.
  Qed.
  *)
  


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

  Check isRREFSolve.

  Extraction "ocaml_test/test.ml" SolveMatrix.
