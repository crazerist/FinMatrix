(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector space
  author    : Zhengpu Shi
  date      : 2024.01

  reference :
  1. 丘维声《高等代数》，第2版，清华大学出版社，2019

  remark    :
  1. contents
  * Linearly combination 线性组合
  * leqs (linear equation) 线性方程组
  * lrep (linearly representable) 线性表示
  * lreps 向量组可由向量组“线性表示(线性表出)”
  * vsequiv (Equivalent vectors) 等价向量组，若二者能够互相线性标出
  * lspan 由向量组生成(张成)的子空间
  * ldep (linear depenent) 线性相关
  * lindep (linear indepenent) 线性无关
  * lmis (maximal linearly independent system) 极大线性无关组
  * vectroSpace 向量空间，是线性空间的具体情形。其元素形如 @vec A c。
    (1) 若A为实数，称为 real vector space
    (2) 若A为复数，称为 complex vector space
 *)


Require Export LinearSpace.
Require Export Matrix.
Require Export MatrixGauss.
Require Import IndefiniteDescription. 
Require Import Logic.Classical.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope VectorSpace_scope.


(* ===================================================================== *)
(** ** Linearly combination (线性组合) *)
Section lcomb.
  Context `{HVectorSpace : VectorSpace}.
  Add Field field_inst : (make_field_theory F).

  Notation "0" := Azero : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation "a - b" := ((a + - b)%A) : A_scope.

  Notation vzero := (vzero 0%A).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation vopp := (@vopp _ Aopp).
  Notation "- v" := (vopp v) : vec_scope.
  Notation vsub a b := (a + - b).
  Notation "a - b" := ((a + (-b))%V) : vec_scope.
  Notation vscal := (@vscal _ Amul _).
  Infix "s*" := vscal : vec_scope.
  Notation vdot := (@vdot _ Aadd Azero Amul).

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation "- v" := (Vopp v) : VectorSpace_scope.
  Notation Vsub u v := (u + -v).
  Infix "-" := Vsub : VectorSpace_scope.
  Infix "s*" := Vscal : VectorSpace_scope.
  Notation vsum := (@vsum _ Vadd 0 _).
  
  (** Linear combination of v1,v2, ..., vn by coefficients c1,c2, ..., cn *)
  Definition lcomb {n} (cs : @vec tA n) (vs : @vec V n) : V :=
    vsum (vmap2 Vscal cs vs).

  (** 0 * v1 + 0 * v2 + ... + 0 * vn = 0 *)
  Lemma lcomb_coef_0 : forall {n} (vs : @vec V n), lcomb vzero vs = 0.
  Proof.
    intros. unfold lcomb. apply vsum_eq0. intros. rewrite vnth_vmap2.
    rewrite vnth_vzero. rewrite vs_vscal_0_l. auto.
  Qed.

  (** c1 * 0 + c2 * 0 + ... + cn * 0 = 0 *)
  Lemma lcomb_vec_0 : forall {n} (cs : @vec tA n), lcomb cs (@Vector.vzero _ Vzero _) = 0.
  Proof.
    intros. unfold lcomb. apply vsum_eq0. intros. rewrite vnth_vmap2.
    rewrite vnth_vzero. rewrite vs_vscal_0_r. auto.
  Qed.

  (** (c1 + c2) * v = c1 * v + c2 * v *)
  Lemma lcomb_coef_add : forall {n} (vs : @vec V n) c1 c2,
      lcomb (c1 + c2)%V vs = lcomb c1 vs + lcomb c2 vs.
  Proof.
    intros. unfold lcomb. rewrite vsum_add. apply vsum_eq; intros.
    rewrite !vnth_vmap2. rewrite vnth_vadd. rewrite vs_vscal_aadd. auto.
  Qed.

  (** (- c) * v = - (c * v) *)
  Lemma lcomb_coef_opp : forall {n} (vs : @vec V n) c,
      lcomb (- c)%V vs = - (lcomb c vs).
  Proof.
    intros. unfold lcomb. rewrite vsum_opp. apply vsum_eq; intros.
    rewrite !vnth_vmap2. rewrite vnth_vopp. rewrite vs_vscal_opp. auto.
  Qed.

  (** (c1 - c2) * v = c1 * v - c2 * v *)
  Lemma lcomb_coef_sub : forall {n} (vs : @vec V n) c1 c2,
      lcomb (c1 - c2)%V vs = lcomb c1 vs - lcomb c2 vs.
  Proof.
    intros. rewrite lcomb_coef_add. rewrite lcomb_coef_opp. auto.
  Qed.

  (** (a .* c) .* v = a .* (c .* v) *)
  Lemma lcomb_coef_scal : forall {n} (vs : @vec V n) a c,
      lcomb (a s* c)%V vs = a s* (lcomb c vs).
  Proof.
    intros. unfold lcomb. rewrite vsum_scal_l_ext.
    - apply vsum_eq; intros. rewrite !vnth_vmap2. rewrite vnth_vscal.
      apply vs_vscal_assoc.
    - intros. apply vs_vscal_0_r.
    - intros. apply vs_vscal_vadd.
  Qed.

  (** (veye i) * v = v $ i *)
  Lemma lcomb_coef_veye : forall {n} (vs : @vec V n) i,
      lcomb (veye Azero Aone i) vs = vs.[i].
  Proof.
    intros. unfold lcomb. apply vsum_unique with (i:=i).
    - rewrite vnth_vmap2. rewrite vnth_veye_eq. apply vs_vscal_1_l.
    - intros. rewrite vnth_vmap2. rewrite vnth_veye_neq; auto. apply vs_vscal_0_l.
  Qed.

  (** (insert c i ci) * vs = c * (remove vs i) + ci * (vs.i) *)
  Lemma lcomb_coef_vinsert :
    forall {n} (c : @vec tA n) (vs : @vec V (S n)) (i : fin (S n)) (ci : tA),
      lcomb (vinsert c i ci) vs =
        Vadd (lcomb c (vremove vs i)) (Vscal ci vs.[i]).
  Proof.
    intros. unfold lcomb.
    rewrite (vmap2_vinsert_l (Azero:=Azero)(Bzero:=Vzero)(Czero:=Vzero)).
    rewrite vsum_vinsert. auto.
  Qed.
    
  (** (insert c i 0) * vs = c * (remove vs i) *)
  Lemma lcomb_coef_vinsert_0 :
    forall {n} (c : @vec tA n) (vs : @vec V (S n)) (i : fin (S n)),
      lcomb (vinsert c i Azero) vs = lcomb c (vremove vs i).
  Proof.
    intros. rewrite lcomb_coef_vinsert. rewrite vs_vscal_0_l at 1.
    rewrite vs_vadd_0_r. auto.
  Qed.

  (** (insert c i 0) * vs = (insert c i (-1)) * vs + vs.i *)
  Lemma lcomb_coef_vinsert_neg1 :
    forall {n} (c : @vec tA n) (vs : @vec V (S n)) (i : fin (S n)),
      lcomb (vinsert c i Azero) vs =
        Vadd (lcomb (vinsert c i (Aopp Aone)) vs) (vs i).
  Proof.
    intros. rewrite !lcomb_coef_vinsert. rewrite associative. f_equal.
    replace (vs i) with (Aone s* vs i) at 3 by apply vs_vscal_1_l.
    rewrite <- vs_vscal_aadd. f_equal. field.
  Qed.

  (** (vset cs i a) * vs = cs * vs + (a - cs $ i) * (vs $ i) *)
  Lemma lcomb_coef_vset :
    forall {n} (cs : @vec tA n) (vs : @vec V n) (i : fin n) (a : tA),
      lcomb (vset cs i a) vs = lcomb cs vs + (a - cs i)%A s* (vs i).
  Proof.
    intros. unfold lcomb.
    replace ((a - cs i)%A s* vs i)
      with (vsum (vset (@Vector.vzero _ Vzero n) i ((a - cs i)%A s* vs i))).
    - rewrite vsum_add. f_equal.
      apply veq_iff_vnth. intros j. rewrite !vnth_vmap2. destruct (i ??= j).
      + fin2nat. rewrite !vnth_vset_eq. rewrite <- vs_vscal_aadd. f_equal. ring.
      + fin2nat. rewrite !vnth_vset_neq; auto. rewrite vnth_vzero.
        rewrite vs_vadd_0_r. auto.
    - apply vsum_unique with (i:=i).
      + rewrite vnth_vset_eq. auto.
      + intros. rewrite vnth_vset_neq; auto.
  Qed.

  (** cs * (vset vs i u) = cs * vs + (cs $ i) * (u - vs $ i) *)
  Lemma lcomb_vec_vset :
    forall {n} (cs : @vec tA n) (vs : @vec V n) (i : fin n) (u : V),
      lcomb cs (vset vs i u) = lcomb cs vs + (cs i) s* (u - vs i).
  Proof.
    intros. unfold lcomb.
    replace (cs i s* (u - vs i))
      with (vsum (vset (@Vector.vzero _ Vzero n) i (cs i s* (u - vs i)))).
    - rewrite vsum_add. f_equal. apply veq_iff_vnth. intros j.
      rewrite !vnth_vmap2. destruct (i ??= j).
      + fin2nat. rewrite !vnth_vset_eq. rewrite <- vs_vscal_vadd. f_equal.
        rewrite commutative. rewrite associative. rewrite inverseLeft.
        rewrite vs_vadd_0_r; auto.
      + fin2nat. rewrite !vnth_vset_neq; auto. rewrite vnth_vzero. 
        rewrite vs_vadd_0_r; auto.
    - apply vsum_unique with (i:=i).
      + rewrite vnth_vset_eq. auto.
      + intros. rewrite vnth_vset_neq; auto.
  Qed.

  (** lcomb (vremove cs i) (vremove vs i) = (lcomb cs vs) - (cs.i * vs.i) *)
  Lemma lcomb_vremove_vremove : forall {n} (cs : @vec tA (S n)) (vs : @vec V (S n)) i,
      lcomb (vremove cs i) (vremove vs i) = (lcomb cs vs) - (cs i s* vs i).
  Proof.
    intros. unfold lcomb. rewrite (@vmap2_vremove_vremove _ _ _ Azero Vzero Vzero).
    rewrite vsum_vremove. auto.
  Qed.
  
  (** lcomb (vconsH c cs) vs = c * (vhead vs) + (lcomb cs (vremoveH vs)) *)
  Lemma lcomb_coef_vconsH : forall {n} (cs : @vec tA n) (vs : @vec V (S n)) (c : tA),
      lcomb (vconsH c cs) vs = c s* (vhead vs) + lcomb cs (vremoveH vs).
  Proof.
    intros. unfold lcomb. rewrite vsumS_head. f_equal.
    - rewrite vnth_vmap2. f_equal. rewrite vhead_eq. f_equal. fin.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsH_gt0. fin. Unshelve. fin.
  Qed.
  
  (** lcomb (vconsT cs c) vs = (lcomb cs (vremoveT vs)) + c * (vtail vs) *)
  Lemma lcomb_coef_vconsT : forall {n} (cs : @vec tA n) (vs : @vec V (S n)) (c : tA),
      lcomb (vconsT cs c) vs = lcomb cs (vremoveT vs) + c s* (vtail vs).
  Proof.
    intros. unfold lcomb. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsT_lt. fin.
    - rewrite vnth_vmap2. f_equal.
      rewrite vnth_vconsT_n; auto. rewrite fin2nat_nat2finS; auto.
      Unshelve. fin.
  Qed.

  (** lcomb cs (vconsT vs u) = (lcomb (vremoveT cs) vs) + (vtail cs) * u *)
  Lemma lcomb_vec_vconsT : forall {n} (cs : @vec tA (S n)) (vs : @vec V n) (u : V),
      lcomb cs (vconsT vs u) = lcomb (vremoveT cs) vs + (vtail cs) s* u.
  Proof.
    intros. unfold lcomb. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsT_lt. fin.
    - rewrite vnth_vmap2. f_equal.
      rewrite vnth_vconsT_n; auto. fin. Unshelve. fin.
  Qed.

  (** lcomb cs (vconsH u vs) = (vhead cs) * u + (lcomb (vremoveH cs) vs) *)
  Lemma lcomb_vec_vconsH : forall {n} (cs : @vec tA (S n)) (vs : @vec V n) (u : V),
      lcomb cs (vconsH u vs) = (vhead cs) s* u + lcomb (vremoveH cs) vs.
  Proof.
    intros. unfold lcomb. rewrite vsumS_head. f_equal.
    - rewrite vnth_vmap2. f_equal. rewrite vhead_eq. fin.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. f_equal.
      erewrite vnth_vconsH_gt0. fin. Unshelve. fin.
  Qed.

  (** lcomb (vconsT cs c) (vconsT vs v) = (lcomb cs vs) + c * v *)
  Lemma lcomb_vconsT_vconsT : forall {n} (cs : @vec tA n) (vs : @vec V n) c v,
      lcomb (vconsT cs c) (vconsT vs v) = lcomb cs vs + c s* v.
  Proof.
    intros. unfold lcomb. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros i. rewrite !vnth_vmap2. erewrite !vnth_vconsT_lt. fin.
    - rewrite vnth_vmap2. erewrite !vnth_vconsT_n; auto.
      all: rewrite fin2nat_nat2finS; auto.
      Unshelve. fin. fin.
  Qed.

  (** lcomb (vconsH c cs) (vconsH v vs) = c * v + (lcomb cs vs) *)
  Lemma lcomb_vconsH_vconsH : forall {n} (cs : @vec tA n) (vs : @vec V n) c v,
      lcomb (vconsH c cs) (vconsH v vs) = c s* v + lcomb cs vs.
  Proof.
    intros. unfold lcomb. rewrite vsumS_head. f_equal.
    apply vsum_eq; intros i. rewrite !vnth_vmap2. erewrite !vnth_vconsH_gt0. fin.
    Unshelve. fin. fin.
  Qed.

  (** lcomb (vapp cs ds) (vapp us vs) = (lcomb cs us) + (lcomb ds vs) *)
  Lemma lcomb_vapp_vapp : forall {n m} (cs : @vec tA n) (ds : @vec tA m)
                            (us : @vec V n) (vs : @vec V m),
      lcomb (vapp cs ds) (vapp us vs) = (lcomb cs us) + (lcomb ds vs).
  Proof.
    intros. unfold lcomb. rewrite vmap2_vapp_vapp.
    remember (vmap2 Vscal cs us) as u.
    remember (vmap2 Vscal ds vs) as v.
    apply vsum_vapp.
  Qed.

  (** lcomb (lcomb u D) v = lcomb u (lcomb D v) *)
  (* For example:
     (u1,u2,u3) [D11,D12] [v1]  记作 u*D*v，
                [D21,D22] [v2]
                [D31,D32]
     (u*D)*v = <u,col(D,1)> v1 + <u,col(D,2)> v2
             = (u1D11+u2D21+u3D31)v1 + (u1D12+u2D22+u3D32)v2
     u*(D*v) = u1 <row(D,1),v> + u2 <row(D,2),v> + u3 <row(D,3),v>
             = u1(D11v1+D12v2)+u2(D21v1+D22v2)+u3(D31v1+D32v2) *)
  Lemma lcomb_assoc : forall {r c} (u : @vec tA c) (D : @vec (@vec tA r) c) (v : @vec V r),
      lcomb (fun j => vdot u (fun i => D i j)) v = lcomb u (fun i : fin c => lcomb (D i) v).
  Proof.
    intros. unfold lcomb, vdot, vmap2.
    pose proof (vsum_vsum c r (fun i j => Vscal (Amul (u i) (D i j)) (v j))).
    match goal with
    | H: ?a1 = ?a2 |- ?b1 = ?b2 => replace b1 with a2; [replace b2 with a1|]; auto
    end.
    - f_equal. extensionality i. rewrite vsum_scal_l_ext; intros; auto.
      f_equal. extensionality j. rewrite vs_vscal_assoc. auto.
      apply vs_vscal_0_r. apply vs_vscal_vadd.
    - f_equal. extensionality i. rewrite vsum_scal_r_ext; intros; auto.
      apply vs_vscal_0_l. apply vs_vscal_aadd.
  Qed.

  (** (∃ ds, vs = fun i => lcomb ds.i vs) -> (∀ i, ∃ cs, lcomb cs vs = vs.i) *)
  Lemma lcomb_any_ex_imply_all_ex : forall {r s} (us : @vec V r) (vs : @vec V s),
      (exists ds : @vec (@vec tA r) s, vs = fun i => lcomb (ds i) us) ->
      (forall i : fin s, exists cs : @vec tA r, lcomb cs us = vs i).
  Proof. intros. destruct H as [d H]. rewrite H. exists (d i); auto. Qed.

  (* Tips, this proof is tricky:
     1. a special form: ∀ i, ∃ c, lcomb c u = v.i |- ∃ d, v = fun i => lcomb (d.i) u
     2. induction on parameter n and use vconsH to use inductive hypothesis
   *)
  (** (∀ i, ∃ cs, lcomb cs us = vs.i) -> (∃ ds, vs = fun i => lcomb ds.i us) *)
  Lemma lcomb_all_ex_imply_any_ex : forall {r s} (us : @vec V r) (vs : @vec V s),
      (forall i : fin s, exists cs : @vec tA r, lcomb cs us = vs i) ->
        (exists ds : @vec (@vec tA r) s, vs = fun i => lcomb (ds i) us).
  Proof.
    intros. generalize dependent s. induction s; intros.
    - exists (@mkvec0 _ (@Vector.vzero _ Azero r)). apply v0eq.
    - rewrite <- (vconsH_vhead_vremoveH vs). 
      assert (exists cs : vec r, vhead vs = lcomb cs us).
      { specialize (H fin0). destruct H as [cs H]. exists cs. rewrite H. auto. }
      assert (forall i : fin s, exists cs : vec r, lcomb cs us = vremoveH vs i).
      { intros. specialize (H (fSuccRangeS i)). destruct H as [cs H].
        exists cs. rewrite H. auto. }
      destruct H0 as [c0 H0].
      specialize (IHs (vremoveH vs) H1). destruct IHs as [c1 IHs].
      rewrite H0,IHs. unfold vconsH.
      exists (fun i : fin (S s) =>
           match (fin2nat i ??= 0)%nat with
           | left _ => c0
           | right n => c1 (fPredRangeP i (neq_0_lt_stt (fin2nat i) n))
           end).
      apply veq_iff_vnth. intros. destruct (_??=_)%nat; auto.
  Qed.
    
End lcomb.


(* ======================================================================= *)
(** ** linear equation *)
Section leqs.
  Context `{HVectorSpace : VectorSpace}.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vscal).

  (* 含有 s 个方程的 n 元线性方程组。
     其中，a称为系数，x称为未知量，b称为常数项。*)
  Record leqs {n s : nat} := {
      leqs_a : @vec (@vec tA n) s;
      leqs_b : @vec V s
    }.

  (* 若n元有序数组(c1,c2,...,cn)'代入方程后使得每个方程是恒等式，则称它是
     该方程组的一个解。方程组的所有解组成的集合称为这个方程组的解集。
     符合实际问题需要的解称为可行解。*)
  
  (* x is the answer of the equation `e` *)
  Definition leqsAnswer {n s} (e : @leqs n s) (x : @vec V n) : Prop :=
    vmap (fun ai => lcomb ai x) (leqs_a e) = (leqs_b e).
  
  (* n元线性方程组，s和n之间可能的关系：s = n, s < n, s > n *)

  (* 如何求解线性方程组？方程组的消元法。 *)
  (* 线性方程组的初等变换，三种。 *)
  (* 阶梯形方程组，简化阶梯形方程组 *)
  (* Check mrowK. *)
  (* Check mrowSwap. *)
  (* Check mrowKAdd. *)

  (* 可以在这个模块中开发线性方程组的理论 *)
  (* MatrixGauss *)
(* 若n元线性方程组I与II的解集相同，则称方程组I与II同解。
   n元线性方程组的“同解”关系是等价关系。
   不难看出，n元线性方程组经过初等变换1,2,3，得到的方程组与原方程同解。
   因此，经过一系列初等变换变成的简化阶梯形方程组与原线性方程组同解。*)

  (*  在求解过程中，只对线性方程组的系数和常数项进行运算，相应的有系数矩阵和增广矩阵。 *)
   
End leqs.
 

(** ** linearly representable *)
Section lrep.
  Context `{HVectorSpace : VectorSpace}.

  (* Notation "0" := Azero : A_scope. *)
  (* Notation vzero := (vzero 0%A). *)
  (* Notation vadd := (@vadd _ Aadd). *)
  (* Notation vopp := (@vopp _ Aopp). *)
  (* Notation vsub := (@vsub _ Aadd Aopp). *)
  (* Infix "+" := vadd : vec_scope. *)
  (* Notation "- v" := (vopp v) : vec_scope. *)
  (* Infix "-" := vsub : vec_scope. *)

  (* Infix "+" := Vadd : VectorSpace_scope. *)
  (* Notation "0" := Vzero : VectorSpace_scope. *)
  (* Notation "- v" := (Vopp v) : VectorSpace_scope. *)
  (* Notation Vsub u v := (u + -v). *)
  (* Infix "-" := Vsub : VectorSpace_scope. *)
  (* Notation vsum := (@vsum _ Vadd 0 _). *)
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vscal).

  (* 向量 u 可由向量组 vs 线性表示 *)
  Definition lrep {n} (vs : @vec V n) (u : V) : Prop :=
    exists (cs : @vec tA n), lcomb cs vs = u.

  (* 向量 u 不能由向量组 vs 线性表示 *)
  Definition nolrep {n} (vs : @vec V n) (u : V) := (~ (lrep vs u)).

  (* 向量组 vs 中的任意向量 v 可由 vs 线性表示 *)
  Lemma lrep_in : forall {n} (vs : @vec V n), vforall vs (lrep vs).
  Proof. intros. hnf. intros. hnf. exists (veye Azero Aone i). apply lcomb_coef_veye. Qed.
  
End lrep.


(** ** 向量组可由向量组“线性表示(线性表出)” *)
Section lreps.
  Context `{HVectorSpace : VectorSpace}.

  (* Notation "0" := Azero : A_scope. *)
  (* Notation vzero := (vzero 0%A). *)
  (* Notation vadd := (@vadd _ Aadd). *)
  (* Notation vopp := (@vopp _ Aopp). *)
  (* Notation vsub := (@vsub _ Aadd Aopp). *)
  (* Infix "+" := vadd : vec_scope. *)
  (* Notation "- v" := (vopp v) : vec_scope. *)
  (* Infix "-" := vsub : vec_scope. *)

  (* Infix "+" := Vadd : VectorSpace_scope. *)
  (* Notation "0" := Vzero : VectorSpace_scope. *)
  (* Notation "- v" := (Vopp v) : VectorSpace_scope. *)
  (* Notation Vsub u v := (u + -v). *)
  (* Infix "-" := Vsub : VectorSpace_scope. *)
  (* Notation vsum := (@vsum _ Vadd 0 _). *)
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vscal).
  Notation lrep := (@lrep _ _ Vadd Vzero Vscal).

  (* 向量组 vs 可线性表示向量组 us *)
  Definition lreps {r s} (vs : @vec V s) (us : @vec V r) : Prop :=
    vforall us (lrep vs).

  (* 向量组 us 不能由向量组 vs 线性表示 *)
  Definition nolreps {r s} (vs : @vec V r) (us : @vec V s) := (~ (lreps vs us)).

  (** lreps is reflexive *)
  Lemma lreps_refl : forall {r} (vs : @vec V r), lreps vs vs.
  Proof.
    intros. unfold lreps, vforall, lrep. intros.
    exists (veye Azero Aone i). rewrite lcomb_coef_veye. auto.
  Qed.

  (** If `us` could represent `vs` and `vs` could represent `u`, then `us` could
      represent `u` *)
  Lemma lreps_lrep : forall {r s} (us : @vec V r) (vs : @vec V s) (u : V),
      lreps us vs -> lrep vs u -> lrep us u.
  Proof.
    intros. unfold lreps, vforall in H. unfold lrep in *.
    destruct H0 as [c H0]. rewrite <- H0.
    apply (lcomb_all_ex_imply_any_ex (Azero:=Azero)) in H.
    destruct H as [d H]. rewrite H.
    exists (fun i => vsum Aadd Azero (vmap2 Amul c (fun j => d j i))).
    rewrite <- lcomb_assoc. f_equal.
  Qed.

  (** lreps is transitive *)
  Lemma lreps_trans :
    forall {r s t} (us : @vec V r) (vs : @vec V s) (ws : @vec V t),
      lreps us vs -> lreps vs ws -> lreps us ws.
  Proof.
    (* 丘老师的证明与此不同，也许我的证明更简单一些。 *)
    intros. unfold lreps, vforall. intros. apply lreps_lrep with (vs:=vs); auto.
  Qed.
  
End lreps.


(* ===================================================================== *)
(** ** Equivalent vectors *)
Section vsequiv.
  Context `{HVectorSpace : VectorSpace}.
  Notation lreps := (@lreps _ _ Vadd Vzero Vscal).

  (** Two vector systems `us` and `vs` are equivalent *)
  Definition vsequiv {r s} (us : @vec V r) (vs : @vec V s) : Prop :=
    lreps us vs /\ lreps vs us.

  Infix "\~" := vsequiv (at level 70).
  
  Lemma vsequiv_refl : forall {n} (vs : @vec V n), vs \~ vs.
  Proof. intros. hnf. split; apply lreps_refl. Qed.

  Lemma vsequiv_sym : forall {r s} (us : @vec V r) (vs : @vec V s), us \~ vs -> vs \~ us.
  Proof. intros. hnf in *. destruct H; auto. Qed.

  Lemma vsequiv_trans : forall {r s t} (us : @vec V r) (vs : @vec V s) (ws : @vec V t),
      us \~ vs -> vs \~ ws -> us \~ ws.
  Proof.
    intros. hnf in *. destruct H,H0. split.
    apply lreps_trans with vs; auto.
    apply lreps_trans with vs; auto.
  Qed.
  
End vsequiv.


(* ===================================================================== *)
(** ** Span (由向量组生成(张成)的子空间 *)
Section lspan.
  Context `{HVectorSpace : VectorSpace}.
  Notation lrep := (@lrep _ _ Vadd Vzero Vscal).
  Notation vsequiv := (@vsequiv _ _ Vadd Vzero Vscal).

  Instance lspan_Struct {n} (vs : @vec V n) : SubSpaceStruct (lrep vs).
  Proof.
    unfold lrep. constructor.
    - exists (vzero Azero). apply lcomb_coef_0.
    - intros. pose proof u.prf; pose proof v.prf; simpl in *.
      destruct H as [c H], H0 as [c0 H0]. rewrite <- H, <- H0.
      exists (@vadd _ Aadd _ c c0). apply lcomb_coef_add.
    - intros. pose proof v.prf; simpl in *.
      destruct H as [c H]. rewrite <- H.
      exists (@vscal _ Amul _ a c).
      apply lcomb_coef_scal.
  Qed.

  (** 由向量组 vs 张成的子空间，记作 <vs> 或 <v1,v2,...,vn> *)
  #[export] Instance lspan {n} (vs : @vec V n) : VectorSpace Hadd Hzero Hopp Hscal :=
    makeSubSpace (lspan_Struct vs).

End lspan.

          
(* 延长组相关，则缩短组必相关 *)
(* 缩短组无关，则延长组必无关   *)
(* 列多可由列少线性表出，则列多相关 *)
(* ===================================================================== *)
(** ** Linear Dependent, Linear Independent *)
Section ldep.
  Context `{HVectorSpace : VectorSpace}.
  Context {AeqDec : Dec (@eq tA)}.
  Context {VeqDec : Dec (@eq V)}.
  

  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * / b).
  Infix "/" := Adiv : A_scope.

  Infix "+" := Vadd : VectorSpace_scope.
  Notation "0" := Vzero : VectorSpace_scope.
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation vopp := (@vopp _ Aopp).
  Notation "- v" := (vopp v) : vec_scope.
  Notation vsub a b := (a + - b).
  Notation "a - b" := ((a + (-b))%V) : vec_scope.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vscal).
  Notation lrep := (@lrep _ _ Vadd Vzero Vscal).
  Notation nolrep := (@nolrep _ _ Vadd Vzero Vscal).
  Notation lreps := (@lreps _ _ Vadd Vzero Vscal).
  Notation nolreps := (@nolreps _ _ _ Vadd Vzero Vscal).

  Notation vsequiv := (@vsequiv _ _ Vadd Vzero Vscal).
  (** Vectors {v1, v2, ..., vn} are linearly dependent *)
  (* 存在不全为0的系数，使得线性组合等于零向量 *)
  Definition ldep {n} (vs : @vec V n) : Prop :=
    exists (cs : @vec tA n), cs <> vzero /\ lcomb cs vs = 0.

  (* Vectors v1, v2, ..., vn are linearly independent *)
  Definition lindep {n} (vs : @vec V n) : Prop := ~(ldep vs).

  (* 向量组 vs 要么相关，要么无关 *)
  Lemma ldep_or_lindep : forall {n} (vs : @vec V n), ldep vs \/ lindep vs.
  Proof. intros. unfold lindep. apply classic. Qed.
  
  (* 向量线性无关，iff，只有系数全为0的线性组合才会等于零向量。*)
  Lemma lindep_iff_coef0 : forall {n} (vs : @vec V n),
      lindep vs <-> (forall cs, lcomb cs vs = 0 -> cs = vzero).
  Proof.
    intros. unfold lindep, ldep. split; intros.
    - apply not_ex_all_not with (n:=cs) in H. apply not_and_or in H.
      destruct H; try easy. apply NNPP in H. auto.
    - intro. destruct H0 as [c [H0 H0']]. specialize (H c H0'). easy.
  Qed.

  (** 使用线性无关的向量组vs作出的两种线性组合时，必然是相同的系数 *)
  Lemma lindep_imply_coef_same : forall {n} (vs : @vec V n) c1 c2,
      lindep vs -> lcomb c1 vs = lcomb c2 vs -> c1 = c2.
  Proof.
    intros. rewrite lindep_iff_coef0 in H. specialize (H (c1 - c2)).
    apply vsub_eq0_iff_eq. apply H. rewrite lcomb_coef_sub. rewrite H0.
    apply vs_vadd_vopp_r.
  Qed.

  (** 若向量组vs线性无关，且向量u可由vs线性表出，则表出方式唯一 *)
  Lemma lindep_imply_coef_uniq : forall {n} (vs : @vec V n) u,
      lindep vs -> lrep vs u -> exists ! cs, u = lcomb cs vs.
  Proof.
    intros. unfold lrep in H0. destruct H0 as [cs H0]. exists cs. hnf. split; auto.
    intros. rewrite <- H0 in H1. apply lindep_imply_coef_same in H1; auto.
  Qed.

  (** 包含零向量的向量组，必定线性相关 *)
  Lemma ldep_if_contain_0 : forall {n} (vs : @vec V n), (exists i, vs i = Vzero) -> ldep vs.
  Proof.
    intros. destruct H as [i H]. hnf. exists (veye Azero Aone i). split.
    - apply veye_neq0. apply field_1_neq_0.
    - rewrite lcomb_coef_veye. auto.
  Qed.
  
  (** 线性无关的向量组，必不含零向量 *)
  Lemma lindep_then_all_not0 : forall {n} (vs : @vec V n),
      lindep vs -> forall i, vs i <> Vzero.
  Proof.
    intros n vs H. apply not_ex_all_not. intro. apply ldep_if_contain_0 in H0; auto.
  Qed.

  (** 单个向量线性相关，iff，该向量为零 *)
  Lemma ldep_vec1_iff_eq0 : forall (vs : @vec V 1), ldep vs <-> vs = (fun i => Vzero).
  Proof.
    intros. split; intros.
    - unfold ldep in H. destruct H as [c [H H']].
      v2e c. apply v1neq_iff in H. cbv in H. cbv in H'.
      rewrite vs_vadd_0_r in H'.
      eapply vs_vscal_eq0_imply_k0_or_v0 in H'. destruct H'; try easy.
      apply v1eq_iff. erewrite nat2finS_eq; auto. apply H0.
    - apply ldep_if_contain_0. exists (nat2finS 0). rewrite H. auto.
  Qed.
  
  (** 单个向量线性无关，iff，该向量不为零 *)
  Lemma lindep_vec1_iff_neq0 : forall (vs : @vec V 1), lindep vs <-> vs <> (fun i => Vzero).
  Proof. intros. unfold lindep. rewrite ldep_vec1_iff_eq0. easy. Qed.
  
  (** 两个原则：
      1. 如果向量组的一个部分组线性相关，那么整个向量组也线性相关
      2. 如果向量组线性无关，那么它的任何一个部分组也线性无关
      表现出来是如下的几组引理
   *)

  (** vs线性相关，则{u,vs}线性相关 *)
  Lemma ldep_imply_vconsH_ldep : forall {n} (vs : @vec V n) (u : V),
      ldep vs -> ldep (vconsH u vs).
  Proof.
    intros. hnf in *. destruct H as [cs [H H0]].
    (* c1v1+c2v2+...+cnvn=0 |- du+d1v1+...+dnvn = 0 *)
    exists (vconsH Azero cs). split.
    - apply vconsH_neq0_iff. auto.
    - rewrite lcomb_vconsH_vconsH. rewrite H0. rewrite vs_vadd_0_r.
      apply vs_vscal_0_l.
  Qed.

  (** vs线性相关，则{vs,u}线性相关 *)
  Lemma ldep_imply_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      ldep vs -> ldep (vconsT vs u).
  Proof.
    intros. hnf in *. destruct H as [cs [H H0]].
    (* c1v1+c2v2+...+cnvn=0 |- d1v1+d2v2+...+dnvn+duvu = 0 *)
    exists (vconsT cs Azero). split.
    - apply vconsT_neq0_iff. auto.
    - rewrite lcomb_vconsT_vconsT. rewrite H0. rewrite vs_vadd_0_l.
      apply vs_vscal_0_l.
  Qed.
  
  (** {u,vs}线性无关，则vs线性无关 *)
  Lemma vconsH_lindep_imply_lindep : forall {n} (vs : @vec V n) (u : V),
      lindep (vconsH u vs) -> lindep vs.
  Proof.
    intros. hnf in *. intros. destruct H. apply ldep_imply_vconsH_ldep; auto.
  Qed.
  
  (** {vs,u}线性无关，则vs线性无关 *)
  Lemma vconsT_lindep_imply_lindep : forall {n} (vs : @vec V n) (u : V),
      lindep (vconsT vs u) -> lindep vs.
  Proof.
    intros. hnf in *. intros. destruct H. apply ldep_imply_vconsT_ldep; auto.
  Qed.

  (** vremoveH vs 线性相关，则 vs 线性相关 *)
  Lemma vremoveH_ldep_imply_ldep : forall {n} (vs : @vec V (S n)),
      ldep (vremoveH vs) -> ldep vs.
  Proof.
    intros. rewrite <- vconsH_vhead_vremoveH. apply ldep_imply_vconsH_ldep; auto.
  Qed.

  (** vremoveT vs 线性相关，则 vs 线性相关 *)
  Lemma vremoveT_ldep_imply_ldep : forall {n} (vs : @vec V (S n)),
      ldep (vremoveT vs) -> ldep vs.
  Proof.
    intros. rewrite <- (vconsT_vremoveT_vtail vs).
    apply ldep_imply_vconsT_ldep. auto.
  Qed.

  (** vs 线性无关，则 vremoveH vs 线性无关 *)
  Lemma lindep_imply_vremoveH_lindep : forall {n} (vs : @vec V (S n)),
      lindep vs -> lindep (vremoveH vs).
  Proof.
    intros. unfold lindep in *. intro. destruct H.
    apply vremoveH_ldep_imply_ldep; auto.
  Qed.

  (** vs 线性无关，则 vremoveT vs 线性无关 *)
  Lemma lindpe_imply_vremoveT_lindep : forall {n} (vs : @vec V (S n)),
      lindep vs -> lindep (vremoveT vs).
  Proof.
    intros. unfold lindep in *. intro. destruct H.
    apply vremoveT_ldep_imply_ldep; auto.
  Qed.

  (** us线性相关，则{us,vs}线性相关 *)
  Lemma ldep_imply_vapp_ldep_L : forall {n m} (us : @vec V n) (vs : @vec V m),
      ldep us -> ldep (vapp us vs).
  Proof.
    intros. hnf in *. destruct H as [cs [H H0]].
    (* c1u1+...+cnun=0 |- e1u1+...+enun + f1v1+...+fmfm = 0 *)
    exists (vapp cs (@Vector.vzero _ Azero m)). split.
    - rewrite vapp_eq0_iff. apply or_not_and. auto.
    - rewrite lcomb_vapp_vapp. rewrite H0. rewrite lcomb_coef_0.
      apply vs_vadd_0_r.
  Qed.

  (** vs线性相关，则{us,vs}线性相关 *)
  Lemma ldep_imply_vapp_ldep_R : forall {n m} (us : @vec V n) (vs : @vec V m),
      ldep vs -> ldep (vapp us vs).
  Proof.
    intros. hnf in *. destruct H as [ds [H H0]].
    (* d1v1+...+dnvn=0 |- e1u1+...+enun + f1v1+...+fmfm = 0 *)
    exists (vapp (@Vector.vzero _ Azero n) ds). split.
    - rewrite vapp_eq0_iff. apply or_not_and. auto.
    - rewrite lcomb_vapp_vapp. rewrite H0. rewrite lcomb_coef_0.
      apply vs_vadd_0_r.
  Qed.

  (** {us,vs}线性无关，则us线性无关 *)
  Lemma vapp_lindep_imply_lindep_L : forall {n m} (us : @vec V n) (vs : @vec V m),
      lindep (vapp us vs) -> lindep us.
  Proof.
    unfold lindep. intros. intro. destruct H. apply ldep_imply_vapp_ldep_L; auto.
  Qed.

  (** {us,vs}线性无关，则vs线性无关 *)
  Lemma vapp_lindep_imply_lindep_R : forall {n m} (us : @vec V n) (vs : @vec V m),
      lindep (vapp us vs) -> lindep vs.
  Proof.
    unfold lindep. intros. intro. destruct H. apply ldep_imply_vapp_ldep_R; auto.
  Qed.
    
  (** vs(n)线性相关，则vs(n+m)线性相关 *)
  Lemma vheadN_ldep_imply_ldep : forall {n m} (vs : @vec V (n + m)),
      ldep (vheadN vs) -> ldep vs.
  Proof.
    intros. rewrite <- vapp_vheadN_vtailN. apply ldep_imply_vapp_ldep_L; auto.
  Qed.
    
  (** vs(m)线性相关，则vs(n+m)线性相关 *)
  Lemma vtailN_ldep_imply_ldep : forall {n m} (vs : @vec V (n + m)),
      ldep (vtailN vs) -> ldep vs.
  Proof.
    intros. rewrite <- vapp_vheadN_vtailN. apply ldep_imply_vapp_ldep_R; auto.
  Qed.
    
  (** vs(n+m)线性无关，则vs(n)线性无关 *)
  Lemma lindep_imply_vheadN_lindep : forall {n m} (vs : @vec V (n + m)),
      lindep vs -> lindep (vheadN vs).
  Proof.
    unfold lindep. intros. intro. destruct H. apply vheadN_ldep_imply_ldep; auto.
  Qed.
    
  (** vs(n+m)线性无关，则vs(m)线性无关 *)
  Lemma lindep_imply_vtailN_lindep : forall {n m} (vs : @vec V (n + m)),
      lindep vs -> lindep (vtailN vs).
  Proof.
    unfold lindep. intros. intro. destruct H. apply vtailN_ldep_imply_ldep; auto.
  Qed.
  
  (** 线性相关 <-> 其中至少有一个向量可以由其余向量线性表示 *)
  Lemma ldep_iff_exist_lrep : forall {n} (vs : @vec V (S n)),
      ldep vs <-> exists i, lrep (vremove vs i) (vs i).
  Proof.
    intros. unfold ldep,lrep. split; intros.
    - destruct H as [c [H H1]]. apply vneq_iff_exist_vnth_neq in H.
      destruct H as [i H]. exists i.
      (* c1v1+c2v2+civi=0 -> d1v1+d2v2=vi. So, d:=(-c1/ci,-c2/ci) *)
      exists (vmap (fun x => Aopp x / (c i)) (vremove c i)).
      rewrite (@vmap_vremove _ _ Azero Azero). rewrite lcomb_vremove_vremove.
      rewrite vnth_vmap. rewrite !vs_vscal_opp at 1. rewrite group_opp_opp.
      rewrite field_mulInvR; auto. rewrite vs_vscal_1_l at 1.
      replace (vmap (fun x => - x / c i)%A c) with (vscal (Amul:=Amul) (- (/ c i))%A c).
      + rewrite lcomb_coef_scal. rewrite H1. rewrite vs_vscal_0_r at 1.
        apply vs_vadd_0_l.
      + apply veq_iff_vnth; intros j. rewrite vnth_vscal, vnth_vmap.
        rewrite !ring_mul_opp_l at 1. f_equal. apply commutative.
    - destruct H as [i [c H]].
      (* c := (c1,c2,..,c(i-1),-1,c(i+1),...,cn) *)
      exists (vinsert c i (Aopp Aone)). split.
      + apply vinsert_neq0_iff. right. apply field_neg1_neq_0.
      + pose proof (lcomb_coef_vinsert_0 c vs i).
        pose proof (lcomb_coef_vinsert_neg1 c vs i).
        rewrite H0 in H1. rewrite H in H1.
        symmetry in H1. apply vs_add_eqR_imply0 in H1. auto.
  Qed.

  (** 线性无关 <-> 其中每一个向量都不能由其余向量线性表示 *)
  Lemma lindep_iff_none_lrep : forall {n} (vs : @vec V (S n)),
      lindep vs <-> forall i, ~ (lrep (vremove vs i) (vs i)).
  Proof.
    intros. unfold lindep. rewrite ldep_iff_exist_lrep. split; intro.
    apply not_ex_all_not; auto. apply all_not_not_ex; auto.
  Qed.

  (** 向量u可以由vs线性表示，则{vs,u}线性相关 *)
  Lemma lrep_imply_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      lrep vs u -> ldep (vconsT vs u).
  Proof.
   intros. unfold lrep,ldep in *. destruct H as [cs H].
   (* c1v1+civi=u |- d1v1+divi+dnu = 0, So, d:=(c1,ci,-1) *)
   exists (vconsT cs (-(1))%A). split.
   - rewrite vconsT_eq0_iff. apply or_not_and. right. apply field_neg1_neq_0.
   - rewrite lcomb_vconsT_vconsT. rewrite H.
     rewrite vs_vscal_opp1. apply vs_vadd_vopp_r.
  Qed.

  (** 向量u可以由vs线性表示，则{u,vs}线性相关 *)
  Lemma lrep_imply_vconsH_ldep : forall {n} (vs : @vec V n) (u : V),
      lrep vs u -> ldep (vconsH u vs).
  Proof.
   intros. unfold lrep,ldep in *. destruct H as [cs H].
   (* c1v1+civi=u |- d1u+d2v2+divi = 0, So, d:=(-1,c2,ci) *)
   exists (vconsH (-(1))%A cs). split.
   - rewrite vconsH_eq0_iff. apply or_not_and. left. apply field_neg1_neq_0.
   - rewrite lcomb_vconsH_vconsH. rewrite H.
     rewrite vs_vscal_opp1 at 1. apply vs_vadd_vopp_l.
  Qed.
  
  (** 设向量组vs线性无关，向量组{vs,u}线性相关，则向量u可由vs线性表示 *)
  Theorem ldep_vconsT_lindep_imply_lrep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> ldep (vconsT vs u) -> lrep vs u.
  Proof.
    intros. unfold lindep, ldep in *. destruct H0 as [cs [H0 H1]].
    destruct (Aeqdec (vtail cs) Azero) as [H2|H2].
    - (* 若 c.n <> 0，则 (c1,c2,...,cn) 不全为0，并且 c1v1+c2v2+..+cnvn=0,
         于是 v1,v2,...,vn 线性相关，与 H 矛盾 *)
      assert (exists cs, cs <> vzero /\ lcomb cs vs = 0); try tauto.
      exists (vremoveT cs). split.
      + apply vremoveT_neq0_if; auto.
      + rewrite lcomb_vec_vconsT in H1. rewrite H2 in H1.
        rewrite vs_vscal_0_l in H1 at 1. rewrite vs_vadd_0_r in H1. auto.
    - (* 从而，u = (-c1/cn)*v1 + (-c2/cn)*v2 + ... *)
      hnf. exists (vscal (Amul:=Amul) (- / vtail cs)%A (vremoveT cs)).
      rewrite lcomb_coef_scal. rewrite lcomb_vec_vconsT in H1.
      remember (lcomb (vremoveT cs) vs) as v1. rewrite vs_vscal_opp.
      apply group_opp_uniq_r in H1. rewrite <- H1. rewrite vs_vscal_vopp.
      rewrite group_opp_opp. rewrite <- vs_vscal_assoc.
      rewrite field_mulInvL; auto. apply vs_vscal_1_l.
  Qed.
  
  (** 设向量组vs线性无关，向量组{u,vs}线性相关，则向量u可由vs线性表示 *)
  Theorem ldep_vconsH_lindep_imply_lrep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> ldep (vconsH u vs) -> lrep vs u.
  Proof.
    intros. unfold lindep, ldep in *. destruct H0 as [cs [H0 H1]].
    destruct (Aeqdec (vhead cs) Azero) as [H2|H2].
    - (* 若 c.1 <> 0，则 (c1,c2,...,cn) 不全为0，并且 c1v1+c2v2+..+cnvn=0,
         于是 v1,v2,...,vn 线性相关，与 H 矛盾 *)
      assert (exists cs, cs <> vzero /\ lcomb cs vs = 0); try tauto.
      exists (vremoveH cs). split.
      + apply vremoveH_neq0_if; auto.
      + rewrite lcomb_vec_vconsH in H1. rewrite H2 in H1.
        rewrite vs_vscal_0_l in H1 at 1. rewrite vs_vadd_0_l in H1. auto.
    - (* 从而，u = (-c1/c1)*v1 + (-c2/c1)*v2 + ... *)
      hnf. exists (vscal (Amul:=Amul) (- / vhead cs)%A (vremoveH cs)).
      rewrite lcomb_coef_scal. rewrite lcomb_vec_vconsH in H1.
      remember (lcomb (vremoveH cs) vs) as v1. rewrite vs_vscal_opp.
      rewrite <- vs_vscal_vopp. apply group_opp_uniq_r in H1. rewrite H1.
      rewrite <- vs_vscal_assoc. rewrite field_mulInvL; auto. apply vs_vscal_1_l.
  Qed.
  
  (** 设向量组vs线性无关，则：向量u可由vs线性表示，当且仅当，向量组{vs,u}线性相关 *)
  Corollary lrep_iff_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> (lrep vs u <-> ldep (vconsT vs u)).
  Proof.
    intros. split; intros.
    - apply lrep_imply_vconsT_ldep; auto.
    - apply ldep_vconsT_lindep_imply_lrep; auto.
  Qed.
  
  (** 设向量组vs线性无关，则：向量u可由vs线性表示，当且仅当，向量组{u,vs}线性相关 *)
  Corollary lrep_iff_vconsH_ldep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> (lrep vs u <-> ldep (vconsH u vs)).
  Proof.
    intros. split; intros.
    - apply lrep_imply_vconsH_ldep; auto.
    - apply ldep_vconsH_lindep_imply_lrep; auto.
  Qed.

  (* 此性质直观的理解是：线性相关的向量组调整顺序后仍然相关。此处仅仅是头尾两个位置 *)
  (** 向量{u,vs}线性相关，当且仅当，向量组{vs,u}线性相关 *)
  Corollary vconsH_ldep_iff_vconsT_ldep : forall {n} (vs : @vec V n) (u : V),
      ldep (vconsH u vs) <-> ldep (vconsT vs u).
  Proof.
    intros. destruct (ldep_or_lindep vs).
    - split; intros.
      + apply ldep_imply_vconsT_ldep; auto.
      + apply ldep_imply_vconsH_ldep; auto.
    - split; intros.
      + apply lrep_iff_vconsH_ldep in H0; auto. apply lrep_iff_vconsT_ldep; auto.
      + apply lrep_iff_vconsT_ldep in H0; auto. apply lrep_iff_vconsH_ldep; auto.
  Qed.
  
  (** 设向量组vs线性无关，则：向量u不能由vs线性表示，当且仅当，向量组{vs,u}线性无关 *)
  Corollary nolrep_iff_vconsT_lindep : forall {n} (vs : @vec V n) (u : V),
      lindep vs -> (nolrep vs u <-> lindep (vconsT vs u)).
  Proof.
    intros. unfold nolrep, lindep. apply not_iff_compat.
    apply lrep_iff_vconsT_ldep; auto.
  Qed.


  (* 设v1,v2,...,vs线性无关，并且
     u1 = a11v1 + ... + a1svs,
     ...
     us = as1v1 + ... + assvs,
     证明：u1,...,us线性无关的充要条件是
           |a11 ... a1s|
     |A| = |...        | <> 0
           |as1 ... ass|
     
     于是，以下命题互相等价。
     (1) 向量组 v1,v2,...,vs 线性无关
     (2) 上述齐次线性方程组只有零解
     (3) |A| <> 0
   *)

  (** p90, 例7，替换定理：
      设向量组v1,...,vn线性无关，u=c1v1+...+cnvn。若ci<>0，则用u替换vi后得到的
      向量组v1,...,v(i-1),u,v(i+1),...,vn也线性相关 *)
  Lemma lindep_subst : forall {n} (vs : @vec V n) (cs : @vec tA n) (i : fin n),
      lindep vs -> cs i <> Azero -> lindep (vset vs i (lcomb cs vs)).
  Proof.
    intros. unfold lindep, ldep in *. intro. destruct H. destruct H1 as [ds [H1 H2]].
    (* Let cs=c1,c2,...,cn; ds=d1,d2,...,dn. That is,
       d1v1+d2v2+...+di(c1v1+c2v2+...+cnvn) + ... + dnvn = 0
       ---------------------------------------------------------------------
       cs' := {d1,d2,...,d(i-1),0,d(i+1),...,dn} + di*{c1,c2,...,cn} *)
    exists (vadd (vset ds i Azero) (vscal (Amul:=Amul) (ds i) cs)). split.
    - apply vneq_iff_exist_vnth_neq in H1. destruct H1 as [j H1].
      apply vneq_iff_exist_vnth_neq.
      destruct (i ??= j).
      + (* if i = j, then: 0 + ds.i*cs.i <> 0 *)
        fin2nat. rewrite <- e in *.
        exists i. rewrite vnth_vadd. rewrite vnth_vset_eq. rewrite identityLeft.
        rewrite vnth_vscal. rewrite vnth_vzero in *.
        apply field_mul_neq0_iff; auto.
      + (* if i <> j, case (ds.i =? 0) *)
        fin2nat. destruct (Aeqdec (ds i) Azero).
        * (* if ds.i = 0, ds.j <> 0, then: ds.j + 0 <> 0 *)
          exists j. rewrite e. rewrite vscal_0_l. rewrite vadd_0_r.
          rewrite vnth_vset_neq; auto.
        * (* if ds.i <> 0, then: 0 + ds.i*cs.i <> 0 *)
          exists i. rewrite vnth_vadd. rewrite vnth_vset_eq. rewrite vnth_vscal.
          rewrite identityLeft. apply field_mul_neq0_iff; auto.
    - rewrite <- H2 at 2.
      rewrite lcomb_coef_add. rewrite lcomb_coef_scal. rewrite lcomb_coef_vset.
      rewrite lcomb_vec_vset. rewrite vs_vscal_vadd.
      rewrite associative. f_equal. rewrite commutative. f_equal.
      rewrite vs_vscal_aadd. rewrite vs_vscal_vopp at 1. rewrite vs_vscal_opp at 1.
      rewrite vs_vscal_0_l at 1. apply vs_vadd_0_l.
  Qed.

End ldep.


Section basis.
  Context `(ss : SubSpaceStruct).
  Notation lrep := (@lrep _ _ Vadd Vzero Vscal).
  Notation lindep := (@lindep _ Azero _ Vadd Vzero Vscal).

  Definition basis {t}  (vs : @vec V t) :=
    lindep vs /\ ss_eq ss (lspan_Struct vs).

  Definition dim (t : nat) : Prop :=
    exists vs : @vec V t, basis vs.

End basis.

Section basis_theory.
  Context `(ss : SubSpaceStruct).
  Context `{P' : V -> Prop}.
  Context `(ss' : @SubSpaceStruct tA Aadd Azero Aopp Amul Aone Ainv F V Vadd Vzero Vopp Vscal HVectorSpace P').

  Lemma sseq_dim :
    ss_eq ss ss' -> (forall k, dim ss k <-> dim ss' k).
  Proof.
    split; unfold dim; intros.
    - destruct H0 as [cs H0]. unfold basis in *. destruct H0 as [H0 H1].
      exists cs. split; auto. unfold ss_eq in *. intros. split; intros.
      + rewrite <- H1. rewrite H. auto.
      + rewrite <- H. rewrite H1. auto.
    - destruct H0 as [cs H0]. unfold basis in *. destruct H0 as [H0 H1].
      exists cs. split; auto. unfold ss_eq in *. intros. split; intros.
      + rewrite <- H1. rewrite <- H. auto.
      + rewrite H. rewrite H1. auto. 
  Qed.

End basis_theory.

(* ===================================================================== *)
(** ** Maximal linearly independent system 极大线性无关组 *)
Section lmis.
  Context `{HVectorSpace : VectorSpace}.
  Context {AeqDec : Dec (@eq tA)}.
  Context {VeqDec : Dec (@eq V)}.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vscal).
  Notation lrep := (@lrep _ _ Vadd Vzero Vscal).
  Notation lreps := (@lreps _ _ Vadd Vzero Vscal).
  Notation ldep := (@ldep _ Azero _ Vadd Vzero Vscal).
  Notation lindep := (@lindep _ Azero _ Vadd Vzero Vscal).
  Notation vsequiv := (@vsequiv _ _ Vadd Vzero Vscal).

  (** 向量组 ms 是向量组 vs 的极大线性无关组 *)
  Definition lmis {n s} (vs : @vec V n) (ms : @vec V s) : Prop :=
    vmems ms vs /\
      lindep ms /\
      (vforall vs (fun v => ~(vmem ms v) -> ldep (vconsT ms v))) .

  (** 向量组与其极大线性无关组等价 *)
  Lemma lmis_vsequiv_self : forall {n s} (vs : @vec V n) (ms : @vec V s),
      lmis vs ms -> vsequiv vs ms.
  Proof.
    intros. unfold lmis, vsequiv in *. destruct H as [H [H1 H2]].
    unfold vmems,vmem,vexist,vforall,lreps,vforall in *. split.
    - intros. pose proof (lrep_in vs). unfold vforall in H0.
      specialize (H i). destruct H as [j H]. rewrite <- H. auto.
    - intros. specialize (H2 i). pose proof (vmem_dec ms (vs i)).
      destruct H0 as [H0|H0].
      + destruct H0 as [j H0]. rewrite <- H0. apply lrep_in.
      + epose proof (lrep_iff_vconsT_ldep (vs i) H1). apply H3; auto.
  Qed.

  (** 向量组的任意两个极大线性无关组等价 *)
  Corollary lmis_vsequiv_any :
    forall {n s t} (vs : @vec V n) (ms1 : @vec V s) (ms2 : @vec V t),
      lmis vs ms1 -> lmis vs ms2 -> vsequiv ms1 ms2.
  Proof.
    intros. apply lmis_vsequiv_self in H, H0.
    apply vsequiv_trans with vs; auto. apply vsequiv_sym; auto.
  Qed.
  
  (** 向量u可由向量组vs线性表出当且仅当u可由vs的一个极大线性线性无关组线性表出 *)
  Corollary lrep_iff_lrepByLmis :
    forall {n s} (vs : @vec V n) (ms : @vec V s) (u : V),
      lmis vs ms -> (lrep vs u <-> lrep ms u).
  Proof.
    intros. apply lmis_vsequiv_self in H. unfold vsequiv in H. destruct H.
    split; intros. apply (lreps_lrep H0 H1). apply (lreps_lrep H H1).
  Qed.
  
End lmis.

(*
(* ===================================================================== *)
(** ** Basis *)
Section lbasis.
  Context `{HVectorSpace : VectorSpace}.
  Notation lcomb := (@lcomb _ _ Vadd Vzero Vscal).
  Notation lindep := (@lindep _ Azero _ Vadd Vzero Vscal).
  Notation lspan := (@lspan _ _ Vadd Vzero Vscal).

  (** Elements v1,v2,...,vn of V are said to consistute a basis of V *)
  Definition lbasis {n} (vs : @vec V n) : Prop :=
    lindep vs /\ lspan vs.

  (** Elements v1, v2, . . . , vn of a linear space V constitute a basis of 
      that linear space if and only if, given any element u of V , there exist 
      uniquely determined scalars c1, c2, . . . , cn such that
      u = c1v1 + c2v2 + · · · + cnvn  *)
  Theorem lbasis_if_unique_cs : forall {n} (vs : @vec V n),
      lbasis vs <-> forall u : V, exists! (cs : @vec tA n), lcomb cs vs = u.
  Proof.
    intros. split; intros.
    - hnf in H. destruct H as [H H']. hnf in H'. specialize (H' u).
      rewrite <- unique_existence. split; auto.
      hnf. intros c1 c2 H1 H2. rewrite <- H2 in H1.
      apply lindep_imply_coef_uniq in H1; auto.
    - hnf. split.
      + apply lindep_iff_unique0. intros. specialize (H Vzero).
        apply unique_existence in H. destruct H. hnf in H1.
        erewrite H1; auto. apply lcomb_c0_eq0.
      + unfold lspan. intros. specialize (H u). destruct H as [c [H H']].
        exists c; auto.
  Qed.
    
End lbasis.


(** ** Linear Transformations *)
Section ltrans.
  Context `{HField : Field tA Aadd Azero Aopp Amul Aone Ainv}.
  Context `(HV : @VectorSpace tA Aadd Azero Aopp Amul Aone Ainv HField
                   V Vadd Vzero Vopp Vscal).
  Context `(HW : @VectorSpace tA Aadd Azero Aopp Amul Aone Ainv HField
                   W Wadd Wzero Wopp Wscal).
  Notation Vsub u v := (Vadd u (Vopp v)).
  Notation Wsub u v := (Wadd u (Wopp v)).

  (* Let V and W be linear spaces over some field K. tA function T : V → W is said 
     to be a linear transformation if T (u + v) = T (u) + T (v) and T (cv) = cT (v) 
     for all elements u and v of V and for all elements c of K. *)
  Definition ltrans (T : V -> W) : Prop :=
    (forall u v, T (Vadd u v) = Wadd (T u) (T v)) /\ (forall v c, T (Vscal c v) = Wscal c (T v)).

  (** ltrans T -> T(u + v) = T(u) + T(v) *)
  Lemma ltrans_add : forall (T : V -> W),
      ltrans T -> forall u v, T (Vadd u v) = Wadd (T u) (T v).
  Proof. intros. hnf in H. destruct H; auto. Qed.

  (** ltrans T -> T(a * v) = a * T(v) *)
  Lemma ltrans_scal : forall (T : V -> W),
      ltrans T -> forall a v, T (Vscal a v) = Wscal a (T v).
  Proof. intros. hnf in H. destruct H; auto. Qed.

  (** ltrans T -> T(- v) = - T(v) *)
  Lemma ltrans_opp : forall (T : V -> W),
      ltrans T -> forall v, T (Vopp v) = Wopp (T v).
  Proof.
    intros. hnf in H. destruct H; auto.
    rewrite <- !vs_vscal_opp1. rewrite H0. rewrite vs_vscal_opp1. auto.
  Qed.

  (** ltrans T -> T(u - v) = T(u) - T(v) *)
  Lemma ltrans_sub : forall (T : V -> W),
      ltrans T -> forall u v, T (Vsub u v) = Wsub (T u) (T v).
  Proof.
    intros. hnf in H. rewrite ltrans_add; auto. rewrite ltrans_opp; auto.
  Qed.
  
  (** ltrans T -> T(0) = 0 *)
  Lemma ltrans_zero : forall (T : V -> W), ltrans T -> T Vzero = Wzero.
  Proof.
    intros. hnf in H.
    replace (Vzero) with (Vsub Vzero Vzero) by group.
    rewrite ltrans_sub; auto. group.
  Qed.
    
  (** T (c1v1 + c2v2 + · · · + cnvn) 
      = T (c1v1) + T (c2v2) + · · · + T (cnvn)
      = c1w1 + c2w2 + · · · + cnwn *)
  Lemma ltrans_linear : forall {n} (T : V -> W) (cs : @vec tA n)
                           (v : @vec V n) (w : @vec W n),
      ltrans T -> (forall i, w$i = T(v$i)) ->
      T (lcomb (Vadd:=Vadd)(Vzero:=Vzero)(Vscal:=Vscal) cs v) =
        lcomb (Vadd:=Wadd)(Vzero:=Wzero)(Vscal:=Wscal) cs w.
  Proof.
    intros. unfold lcomb.
    apply eq_trans with
      (vsum (Aadd:=Wadd)(Azero:=Wzero) (vmap T (vmap2 Vscal cs v))).
    - rewrite <- (vsum_vmap (Aadd:=Vadd)(Azero:=Vzero)); auto.
      apply ltrans_zero; auto. apply ltrans_add; auto.
    - apply vsum_eq; intros. rewrite !vnth_vmap, !vnth_vmap2.
      rewrite ltrans_scal; auto. rewrite H0. auto.
  Qed.
  
End ltrans.
*)

(** ** 向量的范数，赋范向量空间 *)


(* ===================================================================== *)
(** ** Vector Space *)

(** Vector forms a linear space (called `Vector Space`) *)
Section vectorSpace.
  Context `{HField : Field tA Aadd Azero Aopp Amul Aone Ainv}.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vscal := (@vscal _ Amul).

  #[export] Instance vectorSpace {n : nat} :
    VectorSpace (V:=vec n) vadd vzero vopp vscal.
  Proof.
    constructor; try apply vadd_AGroup; intros.
    apply vscal_1_l. rewrite vscal_assoc; auto.
    apply vscal_add. apply vscal_vadd.
  Qed.

End vectorSpace.
Arguments vectorSpace {tA Aadd Azero Aopp Amul Aone Ainv} HField {n}.

Section props.
  Context `{HField : Field tA Aadd Azero Aopp Amul Aone Ainv}.
  Notation vectorSpace := (vectorSpace HField).

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  Notation vopp := (@vopp _ Aopp).
  Notation "- v" := (vopp v) : vec_scope.
  Notation vsub a b := (a + - b).
  Notation "a - b" := ((a + (-b))%V) : vec_scope.
  Notation vscal := (@vscal _ Amul).
  Notation vsum := (@vsum _ Aadd Azero).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation lcomb := (@lcomb _ _ vadd vzero vscal).
  Notation lrep := (@lrep _ _ vadd vzero vscal).
  Notation ldep := (@ldep _ Azero _ vadd vzero vscal).
  Notation lindep := (@lindep _ Azero _ vadd vzero vscal).

  (** (lcomb cs vs).i = ∑(vmap2 Amul cs (vcol vs i)) *)
  Lemma vnth_lcomb : forall {n r} (cs : @vec tA r) (vs : mat tA r n) (i : fin n),
      (lcomb cs vs) i = vsum (vmap2 Amul cs (mcol vs i)).
  Proof. intros. unfold lcomb. rewrite vnth_vsum. auto. Qed.

  (** lcomb over vectors from `vmap2 vapp us vs` *)
  Lemma lcomb_vec_vmap2_vapp :
    forall (m n r : nat) (cs : @vec tA r)
      (us : @mat tA r m) (vs : @mat tA r n) (i : fin (m + n)),
      lcomb cs (vmap2 vapp us vs) i = vapp (lcomb cs us) (lcomb cs vs) i.
  Proof.
    intros. rewrite vnth_lcomb. destruct (fin2nat i ??< m).
    - rewrite vnth_vapp_l with (H:=l). unfold lcomb.
      rewrite vnth_vsum. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. rewrite !vnth_vscal. f_equal. rewrite !vnth_mcol.
      rewrite vnth_vmap2. rewrite vnth_vapp_l with (H:=l); auto.
    - assert (m <= fin2nat i). lia. rewrite vnth_vapp_r with (H:=H). unfold lcomb.
      rewrite vnth_vsum. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. rewrite !vnth_vscal. f_equal. rewrite !vnth_mcol.
      rewrite vnth_vmap2. rewrite vnth_vapp_r with (H:=H). auto.
  Qed.

  (** F^n的下述子集U是一个子空间 U = {(a1,...,ak,0,...,0) | ai ∈ F, 1 <= k < n } *)
  Section topKWithZero_SubSpace.
    Context {n k : nat}.
    Context {Hk : 1 <= k < n}.

    Instance topKWithZero_SubSpaceStruct
      : SubSpaceStruct
          (fun v => forall (i:fin n),
               if (fin2nat i ??> k)%nat then v i = Azero else True).
    Proof.
      constructor; intros.
      - destruct (_??<_); auto.
      - destruct (_??<_); auto. rewrite vnth_vadd.
        pose proof (u.prf). pose proof (v.prf). simpl in *.
        specialize (H i). specialize (H0 i).
        destruct (_??<_) in H,H0; try lia. rewrite H,H0. apply identityLeft.
      - destruct (_??<_); auto. rewrite vnth_vscal.
        pose proof (v.prf). simpl in *. specialize (H i).
        destruct (_??<_) in H; try lia. rewrite H. apply ring_mul_0_r.
    Qed.

    #[export] Instance topKWithZero_SubSpace : VectorSpace Hadd Hzero Hopp Hscal :=
      makeSubSpace topKWithZero_SubSpaceStruct.
  End topKWithZero_SubSpace.

  (** F^n的下述子集U是一个子空间 U = {(a1,0,a3,0,...0,an) | ai ∈ F, i=1,3,...,n} *)
  Section oddWithZero_SubSpace.
    Context {n : nat}.
    
    Instance oddWithZero_SubSpaceStruct
      : SubSpaceStruct
          (fun v => forall (i : fin n),
               if ((fin2nat i mod 2) ??= 0)%nat then v i = Azero else True).
    Proof.
      constructor; intros.
      - destruct (_??=_)%nat; auto.
      - destruct (_??=_)%nat; auto. rewrite vnth_vadd.
        pose proof (u.prf). pose proof (v.prf). hnf in H,H0.
        specialize (H i). specialize (H0 i).
        destruct (_??=_)%nat in H,H0; try lia. rewrite H,H0. apply identityLeft.
      - destruct (_??=_)%nat; auto. rewrite vnth_vscal.
        pose proof (v.prf). hnf in H. specialize (H i).
        destruct (_??=_)%nat in H; try lia. rewrite H. apply ring_mul_0_r.
    Qed.

    #[export] Instance oddWithZero_SubSpace : VectorSpace Hadd Hzero Hopp Hscal :=
      makeSubSpace oddWithZero_SubSpaceStruct.
  End oddWithZero_SubSpace.

  (** 添加或去掉向量的一些分量构成的延伸组与缩短组的一对性质：
      1. 如果向量组线性无关，那么把每个向量在相同位置添上m个分量得到的延伸组也线性无关
      2. 如果向量组线性相关，那么把每个向量在相同位置去掉m个分量得到的缩短组也线性相关 

      如何表示“延伸组和缩短组”？
      1. 如何表示“延伸的向量”，“缩短的向量”？
      (1) 在头部加入/去掉数个元素，在尾部加入/去掉数个元素，在任意位置加入/去掉数个元素
      (2) 在任意位置的操作包含了头部或尾部。
      3. 如何表示“延伸组”，“缩短组”？
      (1) 关键是要对向量组在相同的位置进行操作。
      (2) 还可以换一种思路，不进行具体的操作，但是可以判断两个向量是否具有“延伸组”或
      “缩短组”的关系？

      给定v1,...,vs，记其延伸组为 v1',...,vs'，
      则从 k1v1'+...ksvs'=0 可得到 k1v1+...+ksvs=0。
      若v1,...,vs线性无关，则可知k1=...=ks=0，从而v1',...,vs'也线性无关。
   *)

  (** 若向量组线性无关，每个向量的相同位置添上m个分量后的延伸组线性无关。*)
  Section lindep_extend.


  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * / b).
  Infix "/" := Adiv : A_scope.
    Notation mvmul := (@mvmul tA Aadd 0 Amul).
    Infix "v*" := mvmul : mat_scope.
    
    (** 在每个向量头部都加入数个元素后保持线性无关 *)
    Lemma lindep_extend_head :
      forall {m n r} (us : @vec (@vec tA m) r) (vs : @vec (@vec tA n) r),
        lindep vs -> lindep (vmap2 vapp us vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fAddRangeAddL i)).
      rewrite vnth_vzero in *. rewrite <- H0 at 2.
      rewrite lcomb_vec_vmap2_vapp. erewrite vnth_vapp_r.
      rewrite fAddRangeAddL'_fAddRangeAddL. auto.
      Unshelve. rewrite fin2nat_fAddRangeAddL. lia.
    Qed.

    (** 在每个向量尾部都加入数个元素后保持线性无关 *)
    Lemma lindep_extend_tail :
      forall {m n r} (us : @vec (@vec tA m) r) (vs : @vec (@vec tA n) r),
        lindep us -> lindep (vmap2 vapp us vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fAddRangeR i)).
      rewrite vnth_vzero in *. rewrite <- H0 at 2.
      rewrite lcomb_vec_vmap2_vapp. erewrite vnth_vapp_l.
      rewrite fAddRangeR'_fAddRangeR. auto.
      Unshelve. rewrite fin2nat_fAddRangeR. apply fin2nat_lt.
    Qed.

    (** 对每个向量都插入1个元素后保持线性无关 *)
    Lemma lindep_extend_insert :
      forall {n r} (vs : @vec (@vec tA n) r) (i : fin (S n)) (a : tA),
        lindep vs -> lindep (vmap (fun v => vinsert v i a) vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; intros; auto.
      rewrite veq_iff_vnth. intros j. rewrite veq_iff_vnth in H0.
      destruct (fin2nat j ??< fin2nat i).
      - specialize (H0 (fSuccRange j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. rewrite !vnth_vmap2. f_equal. unfold mcol.
        rewrite !vnth_vmap. erewrite vnth_vinsert_lt. fin.
      - specialize (H0 (fSuccRangeS j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. rewrite !vnth_vmap2. f_equal. unfold mcol.
        rewrite !vnth_vmap. erewrite vnth_vinsert_gt; fin.
        Unshelve. all: fin.
    Qed.

  End lindep_extend.

  (** 若向量组线性相关，每个向量的相同位置去掉m个分量后的延伸组线性相关。*)
  Section ldep_shorten.
    
    (** 在每个向量头部都去掉数个元素后保持线性相关 *)
    Lemma ldep_shorten_head : forall {m n r} (vs : @vec (@vec tA (m + n)) r),
        ldep vs -> ldep (vmap vtailN vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fAddRangeAddL i)). rewrite vnth_vzero in *.
      rewrite <- H0 at 2. rewrite !vnth_lcomb. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. f_equal.
    Qed.
    
    (** 在每个向量尾部都去掉数个元素后保持线性相关 *)
    Lemma ldep_shorten_tail : forall {m n r} (vs : @vec (@vec tA (m + n)) r),
        ldep vs -> ldep (vmap vheadN vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fAddRangeR i)). rewrite vnth_vzero in *.
      rewrite <- H0 at 2. rewrite !vnth_lcomb. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. f_equal.
    Qed.

    (** 对每个向量都删除1个元素后保持线性相关 *)
    Lemma ldep_shorten_delete :
      forall {n r} (vs : @vec (@vec tA (S n)) r) (i : fin (S n)) (a : tA),
        ldep vs -> ldep (vmap (fun v => vremove v i) vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; intros; auto.
      rewrite veq_iff_vnth. intros j. rewrite veq_iff_vnth in H0.
      destruct (fin2nat j ??< fin2nat i).
      - specialize (H0 (fSuccRange j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. f_equal. apply veq_iff_vnth; intros s.
        rewrite !vnth_mcol. rewrite !vnth_vmap.
        rewrite (@vnth_vremove_lt _ Azero); auto. erewrite nth_v2f. fin.
        apply fin2nat_imply_nat2fin. fin.
      - specialize (H0 (fSuccRangeS j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. f_equal. apply veq_iff_vnth; intros s.
        rewrite !vnth_mcol. rewrite !vnth_vmap.
        rewrite (@vnth_vremove_ge _ Azero); auto; try lia.
        + erewrite nth_v2f. f_equal. apply fin2nat_imply_nat2fin.
          rewrite fin2nat_fSuccRangeS. auto.
        + apply fin2nat_lt.
          Unshelve. pose proof (fin2nat_lt j). lia.
          pose proof (fin2nat_lt j). lia.
    Qed.
    
  End ldep_shorten.

  
  (** F^n中的s个向量中的每一个都在这个向量组张成的线性空间中。
      即，vi ∈ <v1,v2,...,vs>, 1<=i<=s, vi∈F^n *)
  Lemma in_lspan : forall {n s} (vs : @vec (@vec tA n) s) i,
      Hbelong (lspan_Struct vs) (vs i).
  Proof. intros. hnf. apply lrep_in. Qed.
  
  (** 在F^n中，任意向量都能由n个线性无关的向量来线性表示 *)
  Lemma lindep_imply_lrep_any : forall {n} (vs : @vec (@vec tA n) n) (u : @vec tA n),
      lindep vs -> lrep vs u.
  Proof.
    intros.
    pose proof (in_lspan vs). unfold Hbelong in H0.
    rewrite lindep_iff_coef0 in H.
    unfold lindep,ldep in H. unfold lrep.
  Admitted.
  
  (** 在F^n中，任意n+1个向量都线性相关 *)
  Lemma ldep_Sn : forall {n} (vs : @vec (@vec tA n) (S n)), ldep vs.
  Proof.
    (* 丘老师的证明：
       考虑齐次线性方程组 x1v1+x2v2+...+x(n-1)v(n-1)=0，
       它的方程个数n小于未知量个数n+1，因此它有非零解。所以vs线性相关。*)

    (* 我的证明（只有思路，尚未完成）：
       1. 前n个向量要么线性相关，要么线性无关。
       (1). 若线性相关，则这n+1个向量是线性相关的；
       (2). 若线性无关，则第n+1个向量可由前n个向量线性表示，于是这n+1个向量线性相关。*)
    intros.
    rewrite <- vconsT_vremoveT_vtail.
    assert ({ldep (vremoveT vs)} + {~ (ldep (vremoveT vs))}).
    (* 此可判定性也许无法证明，因为涉及到存在量词 *) admit.
    destruct H.
    - apply ldep_imply_vconsT_ldep. auto.
    -
      Admitted.
    


  (* 几何空间：
     1. 几何空间可以看成是以原点O为起点的所有向量组成的集合V，它有加法和数量乘法两种运算。
     2. 几何空间V的一个非空子集U如果对于向量的加法和数乘都封闭，则称U是V的一个子空间。
     3. 一条直线l可看成是以O为起点，以l上的点为终点的所有向量组成的集合。
     4. 一个平面π可看成是以O为起点，以π上的点为终点的所有向量组成的集合。
   *)
  
  
  (* 自然基的性质 *)
  Section veyes.
    Context {n : nat}.
    Notation veyes := (veyes 0 1).

    (** 任意向量都能写成自然基的线性组合: v * eyes = v *)
    Lemma lcomb_veyes : forall v : vec n, lcomb v (veyes n) = v.
    Proof.
      intros. unfold lcomb. apply veq_iff_vnth. intros.
      (* (v1(1,0,0) + v2(0,1,0) + v3(0,0,1)).i = v.i *)
      rewrite vnth_vsum.
      (* v1(1,0,0).i + v2(0,1,0).i + v3(0,0,1).i = v.i *)
      apply vsum_unique with (i:=i).
      - rewrite vnth_vmap2. rewrite vnth_vscal. rewrite vnth_veyes_eq.
        apply identityRight.
      - intros. rewrite vnth_vmap2. rewrite vnth_vscal.
        rewrite vnth_veyes_neq; auto. apply ring_mul_0_r.
    Qed.
    
    (** 自然基是线性无关的 *)
    Lemma lindep_veyes : lindep (veyes n).
    Proof.
      intros. unfold lindep, ldep. intro. destruct H as [v [H H0]]. destruct H.
      rewrite lcomb_veyes in H0. auto.
    Qed.

    (** 任意向量 v 都可由自然基线性表示 *)
    Lemma lrep_veyes : forall (v : vec n), lrep (veyes n) v.
    Proof. intros. unfold lrep. exists v. apply lcomb_veyes. Qed.

    (** 任意向量 v，用自然基线性表示的方式唯一 *)
    Lemma lrep_veyes_unique : forall (v : vec n), exists! c, lcomb c (veyes n) = v.
    Proof.
      intros. exists v. split. apply lcomb_veyes. intros. rewrite lcomb_veyes in H. auto.
    Qed.
    
    (* Example ex1_vspan : vspan vecs. *)
    (* Proof. *)
    (*   unfold vspan. intros. exists (mkvec3 (u.1) (u.2) (u.3)). *)
    (*   apply v3eq_iff. cbv. lra. *)
    (* Qed. *)
    
    (* Example ex2_vbasis : vbasis vecs. *)
    (* Proof. *)
    (*   unfold vbasis. split. apply ex1_vlindep. apply ex1_vspan. *)
    (* Qed. *)

  End veyes.
End props.

Section rank.

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
  Notation vscale := (@vscale _ Amul).
  Notation vadde := (@vadde _ Aadd Amul).
  Notation vsum := (@vsum _ vadd vzero _).
  Notation veye := (@veye _ Azero Aone).
  Infix "s*" := vscal : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  
  Notation mat r c := (mat tA r c).
  Notation mat1  := (@mat1 tA Azero Aone).
  Notation mrowSwap := (@mrowSwap tA).
  Notation mrowScale := (@mrowScale _ Amul).
  Notation mrowAdd := (@mrowAdd _ Aadd Amul).
  Notation mmul := (@mmul tA Aadd 0 Amul).
  Notation mmulv := (@mmulv tA Aadd 0 Amul).
  Notation mvmul := (@mvmul tA Aadd 0 Amul).
  Notation mrowSwapM := (@mrowSwapM tA 0 1).
  Notation mrowAddM := (@mrowAddM tA Aadd 0 1).
  Notation mrowScaleM := (@mrowScaleM tA 0 1).
  Infix "*" := mmul : mat_scope.
  Infix "*v" := mmulv : mat_scope.
  Infix "v*" := mvmul : mat_scope.

  Notation lrep := (@lrep _ _ vadd vzero vscal).
  Notation lreps := (@lreps _ _ vadd vzero vscal).
  Notation ldep := (@ldep _ Azero _ vadd vzero vscal).
  Notation lindep := (@lindep _ Azero _ vadd vzero vscal).
  Notation vsequiv := (@vsequiv _ _ vadd vzero vscal).
  Notation lcomb := (@lcomb tA _ vadd vzero  vscal).
  Notation lmis := (@lmis _ Azero _ vadd vzero vscal).
  Notation ldep_or_lindep := (@ldep_or_lindep _ Azero _ vadd vzero vscal _).
  Notation MRT := (@MRT _ Aadd Azero Amul).
  Notation getPivotNum := (@getPivotNum _ Azero _).
  Notation toRREF := (@toRREF  _ Aadd Azero Aopp Amul Ainv _).

  Lemma lcomb_eq :
    forall {n s} (vs : @vec (@vec tA s) n) (cs : vec n),
    lcomb cs vs = cs v* vs.
  Proof.
    intros. unfold lcomb. unfold mvmul, vdot. extensionality i.
    rewrite vnth_vsum. f_equal.
  Qed. 

  Lemma lreps_eq_helper {s n t} (vs : mat n s) (us : mat t s)
  (H : lreps vs us) : mat t n.
  Proof.
    unfold lreps, vforall in H. intro i. specialize H with i. unfold lrep in H.
    apply constructive_indefinite_description in H. destruct H. exact (x).
  Defined.

  Lemma lreps_eq :
    forall {s n t} (vs : @vec (@vec tA s) n) (us : @vec (@vec tA s) t),
    lreps vs us <-> exists Q : mat t n, (Q * vs)%M  = us.
  Proof.
    intros. split; intros.
    - exists (lreps_eq_helper H). apply meq_iff_mnth. intros a b.
      unfold lreps_eq_helper. rewrite mnth_mmul. 
      destruct (constructive_indefinite_description).
      rewrite lcomb_eq in e. rewrite <- e. unfold mvmul. auto.
    - destruct H as [Q H]. unfold lreps, vforall. intros.
      unfold lrep. exists (Q i). rewrite lcomb_eq. rewrite <- H.
      extensionality j. rewrite mnth_mmul. unfold mvmul. auto. 
  Qed.

  

  Lemma lindep_vinsert_lindep :
    forall {n r} (vs : @vec (@vec tA n) r) (v : (@vec tA n)) (i :'I_(S r)),
    lindep (vinsert vs i v) -> lindep vs.
  Proof.
    intros. rewrite lindep_iff_coef0. intros.
    rewrite lindep_iff_coef0 in H.
    specialize H with (@vinsert tA _ cs i Azero)%A.
    assert (lcomb (vinsert cs i Azero) (vinsert vs i v) = vzero).
    - rewrite lcomb_coef_vinsert. erewrite vremove_vinsert. Unshelve. all: fin.
      rewrite H0. rewrite vscal_0_l. rewrite vadd_0_l; auto.
    - apply H in H1. extensionality x. destruct (x ??< i) as [E'|E'].
      + assert (vinsert cs i 0 (fSuccRange x) = vzero (fSuccRange x)) by (rewrite H1; auto).
        rewrite vnth_vzero in *. erewrite vnth_vinsert_lt in H2. Unshelve. all : fin.
      + assert (vinsert cs i 0 (fSuccRangeS x) = vzero (fSuccRangeS x)) by (rewrite H1; auto).
        rewrite vnth_vzero in *. erewrite vnth_vinsert_gt in H2. Unshelve. all : fin.
  Qed.

    (** 向量u可以由vs线性表示，则{vs,u}线性相关 *)
  Lemma lrep_imply_vinsert_ldep :
    forall {n r} (vs : @vec (@vec tA n) r) (v : (@vec tA n)) (i :'I_(S r)),
      lrep vs v -> ldep (vinsert vs i v).
  Proof.
    intros. unfold lrep,ldep in *. destruct H as [cs H].
    (* c1v1+civi=u |- d1v1+divi+dnu = 0, So, d:=(c1,ci,-1) *)
    exists (@vinsert tA _ cs i (Aopp 1)). split.
    - intro. assert (vinsert cs i (Aopp 1) i = vzero i) by (rewrite H0; auto).
      erewrite vnth_vinsert_eq in H1. Unshelve. all : fin.  rewrite vnth_vzero in H1.
      pose proof field_neg1_neq_0. rewrite H1 in H2; contradiction. 
    - rewrite lcomb_coef_vinsert. erewrite vremove_vinsert. rewrite H.
      erewrite vnth_vinsert_eq. rewrite vs_vscal_opp1. apply vs_vadd_vopp_r.
      Unshelve. all : fin.
  Qed.

    (** 设向量组vs线性无关，向量组{vs,u}线性相关，则向量u可由vs线性表示 *)
  Theorem ldep_vinsert_lindep_imply_lrep : 
    forall {n r} (vs : @vec (@vec tA n) r) (v u: (@vec tA n)) (i :'I_(S r)),
      lindep vs -> ldep (vinsert vs i u) -> lrep vs u.
  Proof.
    intros. unfold lindep, ldep in *. destruct H0 as [cs [H0 H1]].
    destruct (classic (cs.[i] =  Azero)) as [H2|H2].
    - (* 若 c.n <> 0，则 (c1,c2,...,cn) 不全为0，并且 c1v1+c2v2+..+cnvn=0,
         于是 v1,v2,...,vn 线性相关，与 H 矛盾 *)
      assert (exists cs, cs <> vzero /\ lcomb cs vs = vzero); try tauto.
      exists (vremove cs i). split.
      + intro. apply H0. extensionality x. rewrite vnth_vzero.
        destruct (x??< i) as [E|E]; [|destruct (i ??< x) as [E'|E']].
        * assert (x < r). { pose proof (fin2nat_lt i). lia. }
          assert (vremove cs i (fPredRange x H4) = vzero (fPredRange x H4)) by (rewrite H3; auto).
          erewrite vnth_vremove_lt in H5; fin. erewrite nth_v2f in H5; fin. Unshelve. all: fin.
        * assert (0 < x) by fin.
          assert (vremove cs i (fPredRangeP x H4) = vzero (fPredRangeP x H4)) by (rewrite H3; auto).
          erewrite vnth_vremove_ge in H5; fin. 2: { pose proof (fin2nat_lt x). fin. }
          Unshelve. all : fin. assert ((S (pred x)) < S r). { pose proof (fin2nat_lt x). lia. }
           rewrite nth_v2f with (H:=H6) in H5; fin.  
          rewrite vnth_vzero in H5. rewrite <- H5. f_equal. apply fin2nat_eq_iff.
          rewrite fin2nat_nat2fin. lia.
        * assert (fin2nat x = i) by lia. apply fin2nat_eq_iff in H4; subst. auto.
      + replace cs with (vinsert (vremove cs i) i cs.[i]) in H1.
        2:{ erewrite vinsert_vremove. auto. Unshelve. all : fin. }
        rewrite lcomb_coef_vinsert in H1. rewrite H2 in H1.
        erewrite vremove_vinsert in H1. Unshelve. 2: fin. erewrite vscal_0_l in H1.
        erewrite vs_vadd_0_r in H1. auto.
    - (* 从而，u = (-c1/cn)*v1 + (-c2/cn)*v2 + ... *)
      hnf. exists (vscal (- / cs.[i])%A (vremove cs i)).
      rewrite lcomb_coef_scal. replace cs with (vinsert (vremove cs i) i cs.[i]) in H1.
      2:{ erewrite vinsert_vremove. auto. Unshelve. all : fin. }
      rewrite lcomb_coef_vinsert in H1. 
      erewrite vremove_vinsert in H1. Unshelve. 2: fin.
      erewrite vnth_vinsert_eq in H1. Unshelve. 2: fin.
      extensionality y. rewrite vnth_vscal.
      assert ((lcomb (vremove cs i) vs + vscal (cs i) u) y = vzero y) by (rewrite H1; auto).
      rewrite vnth_vzero in H3. rewrite vnth_vadd in H3.
      apply group_opp_uniq_r in H3. rewrite <- H3. rewrite vnth_vscal.
      rewrite ring_mul_opp_opp. rewrite <- associative.
      replace (/ cs i * cs i) with 1.
      2: { symmetry. apply field_mulInvL. auto. }
      rewrite field_mul_1_l; auto.
  Qed.


    (** 设向量组vs线性无关，则：向量u可由vs线性表示，当且仅当，向量组{vs,u}线性相关 *)
  Corollary lrep_iff_vinsert_ldep : 
    forall {n r} (vs : @vec (@vec tA n) r) (v: (@vec tA n)) (i :'I_(S r)),
      lindep vs -> (lrep vs v <-> ldep (vinsert vs i v)).
  Proof.
    intros. split; intros.
    - apply lrep_imply_vinsert_ldep; auto.
    - apply ldep_vinsert_lindep_imply_lrep with i; auto.
  Qed.



  Lemma lindep_insert_ldep_lindep :
    forall {n r} (vs : @vec (@vec tA n) r) (v u : (@vec tA n)) (i :'I_(S r)),
    lindep (vinsert vs i v) -> ldep (vinsert vs i (v + u)) -> 
    lindep (vinsert vs i u).
  Proof.
    intros. apply lindep_vinsert_lindep in H as E. intro. apply H. clear H.
    apply lrep_iff_vinsert_ldep with (v:=u) (i:=i) in E as H.
    rewrite <- H in H1. destruct H1 as [cs H1].
    apply lrep_iff_vinsert_ldep with (v:=(v+u)) (i:=i) in E as H'.
    rewrite <- H' in H0. destruct H0 as [cs' H0].
    apply ldep_iff_exist_lrep. eexists i.
    erewrite vremove_vinsert. Unshelve. 2: fin.
    erewrite vnth_vinsert_eq. Unshelve. 2: fin.
    unfold lrep. exists (vadd cs' (vopp cs)).
    rewrite lcomb_eq in *. extensionality x.
    assert ((cs' v* vs) x = (v + u) x) by (rewrite H0; auto).
    assert ((cs v* vs) x = u x) by (rewrite H1; auto).
    unfold mvmul in *. rewrite vnth_vadd in H2.
    rewrite vdot_vadd_l. rewrite vdot_vopp_l.
    rewrite H2. rewrite H3. fin.
  Qed.


  Lemma vmem_eq :
    forall {n s} (M : mat n s) (v : vec s),
      vmem M v <-> exists i : 'I_n, veye i v* M = v.
  Proof.
    unfold vmem, vexist; intros. split; intros.
    - destruct H as [i H]. exists i. extensionality j.
      unfold mvmul. rewrite vdot_veye_l. rewrite <- H. fin.
    - destruct H as [i H]. exists i. rewrite <- H.
      unfold mvmul. extensionality j.
      rewrite vdot_veye_l. fin.
  Qed.

   Definition vmems_eq_helper {n s t: nat} (M : mat n s) (V : mat t s)
    (H : forall i : 'I_t, exists i0 : 'I_n, M i0 = V i ) : mat t n.
  Proof.
    unfold mat. intros i. specialize H with (i:=i).
    apply constructive_indefinite_description in H.
    destruct H as [x  H1]. exact (veye x).
  Defined.

  Lemma vmems_eq :
    forall {n s t} (M : mat n s) (V : mat t s),
    vmems V M <->
    exists P : mat t n, (P * M)%M = V /\ (forall i: 'I_t, exists j, P.[i] = veye j).
  Proof.
    unfold vmems, vmem, vforall, vexist ; intros. split; intros.
    - exists (vmems_eq_helper H). split.
      + apply meq_iff_mnth. intros i j. rewrite mnth_mmul.
        unfold vmems_eq_helper. destruct constructive_indefinite_description.
        rewrite vdot_veye_l. rewrite <- e. fin. 
      + intros. unfold vmems_eq_helper. destruct constructive_indefinite_description.
        exists x. reflexivity.
    - destruct H as [P [H H1]]. specialize H1 with i. destruct H1 as [j H1].
      exists j. rewrite <- H. apply veq_iff_vnth. intros k. rewrite mnth_mmul.
      rewrite H1. rewrite vdot_veye_l. unfold mcol. auto.
  Qed.

  Lemma vmems_lindep_infer :
    forall {n s t} (M : mat n s) (V : mat t s),
    vmems V M -> lindep V ->
    exists P : mat t n, (P * M)%M = V /\ (forall i: 'I_t, exists j, P.[i] = veye j) /\
    (forall j: 'I_n, (exists i, P&[j] = veye i) \/ P&[j]  = vzero).
  Proof.
    intros. assert (H1:=H). rewrite vmems_eq in H1. destruct H1 as [P [H1 H2]]. exists P. repeat split; auto.
    intros; induction t.
    - right. unfold mcol. extensionality b. pose proof (fin2nat_lt b); lia.
    - specialize IHt with (V:=vremoveT V) (P:=vremoveT P). destruct IHt.
      + unfold vmems, vforall, vmem, vexist in *. intros i.
        specialize H with (fSuccRange i). destruct H as [k H]. exists k.
        unfold vremoveT. rewrite H. auto.
      + apply lindpe_imply_vremoveT_lindep. auto.
      + rewrite <- H1. apply meq_iff_mnth. intros a b. unfold vremoveT.
        rewrite !mnth_mmul. auto.
      + intros. specialize H2 with (fSuccRange i). destruct H2 as [k H2].
        exists k. rewrite <- H2. unfold vremoveT. auto.
      + destruct H3 as [k H3]. assert (H4:=H2). specialize H4 with (#t).  destruct H4 as [p H4].
        destruct (classic (p = j)) as [E|E].
        * subst. exfalso. unfold mcol in H3.
          assert (P.[fSuccRange k].[j] = 1). {
            assert (vremoveT P k j = veye k k) by (rewrite <- H3; auto).
            unfold veye in H1. destruct (k ??= k); fin. }
          specialize H2 with (fSuccRange k). destruct H2 as [p H2].
          assert (p = j). { apply NNPP; intro.
            assert (P (fSuccRange k) j = veye p j) by (rewrite H2; auto).
            rewrite H1 in H6. unfold veye in H6. destruct (p ??= j) as [E|E].
            rewrite fin2nat_eq_iff in E. subst. contradiction. apply field_1_neq_0 in H6. auto. }
          subst p. apply H0.
          rewrite ldep_iff_exist_lrep. exists #t. unfold lrep.
          exists (veye k). rewrite lcomb_eq. extensionality b.
          rewrite mnth_mmul. unfold mvmul. rewrite H4.
          rewrite !vdot_veye_l. unfold mcol. unfold vremove. destruct (k ??< #t).
          2: { replace (fin2nat (#t :'I_(S t))) with t in * by fin. pose proof (fin2nat_lt k). lia. }
          rewrite mnth_mmul. rewrite H2. rewrite vdot_veye_l. auto.
        * left. exists (fSuccRange k). extensionality b. unfold mcol in *.
          unfold veye. destruct (classic (b = #t)).
          1:{ subst. rewrite H4. unfold veye. destruct (p ??= j); fin.
              pose proof (fin2nat_lt k). lia. }
          assert (fin2nat b <> t). { intro. apply H5. fin. }
          assert (b < t). { pose proof (fin2nat_lt b). lia. }
          assert  (vremoveT P (fPredRange b H7) j = veye k (fPredRange b H7)) by (rewrite <- H3; auto).
          unfold vremoveT in H8. rewrite fSuccRange_fPredRange in H8. rewrite H8.
          unfold veye. destruct (k ??= fPredRange b H7) as [E0|E0]; destruct (fSuccRange k ??= b) as [E1|E1]; fin.
      + assert (H4:=H2). specialize H4 with (#t).  destruct H4 as [p H4].
         destruct (classic (p = j)) as [E|E].
        * subst. left. exists #t.
          assert (P.[#t].[j] = 1). { rewrite H4. unfold veye. destruct (j??=j); fin. }
          extensionality b. destruct (classic (b = #t)).
          1:{ subst b. unfold mcol. unfold veye. destruct (#t ??= #t); fin. }
          unfold mcol, veye. destruct (#t ??= b).
          1: { exfalso. apply H5; apply fin2nat_eq_iff. fin. } clear n0.
          assert (fin2nat b <> t). { intro. apply H5; fin. }
          assert (b < t). { pose proof (fin2nat_lt b); fin. }
          assert (vremoveT P (fPredRange b H7) j = vzero (fPredRange b H7)).
          { unfold mcol in H3. rewrite <- H3; auto. }
          unfold vremoveT in H8. rewrite vnth_vzero in H8. rewrite <- H8.
          f_equal. fin.
        * right. extensionality b. rewrite vnth_vzero. unfold mcol.
          destruct (classic (b = #t)).
          1:{ subst b. rewrite H4. unfold veye. destruct (p ??= j); fin. }
          assert (fin2nat b <> t). { intro. apply H5; fin. }
          assert (b < t). { pose proof (fin2nat_lt b); fin. }
          assert (vremoveT P (fPredRange b H7) j = vzero (fPredRange b H7)).
          { unfold mcol in H3. rewrite <- H3; auto. }
          unfold vremoveT in H8. rewrite vnth_vzero in H8. rewrite <- H8.
          f_equal. fin.
  Qed.

    Definition lmis_eq_helper {r c t} (M : mat r c) (V : mat t c) 
  (H: vmems V M) (H0 : lindep V)
  (H1 : forall i : 'I_r, ~ vmem V (M i) -> ldep (vconsT V (M i)))
  : mat r t.
  Proof.
    intro a. case (vmem_dec V (M a)) as [Hmem | Hnmem].
    - apply vmem_eq in Hmem. apply constructive_indefinite_description in Hmem. 
      destruct Hmem. exact (veye x).
    - apply H1 in Hnmem. apply lrep_iff_vconsT_ldep with (u:= (M a)) in H0.
      rewrite <- H0 in Hnmem. unfold lrep in Hnmem.
      apply constructive_indefinite_description in Hnmem. destruct Hnmem.
      exact (x).
  Defined.


  Lemma lmis_eq :
    forall {r c t} (M : mat r c) (V : mat t c),
      lmis M V <->
      (vmems V M) /\
      lindep V /\
      exists Q : mat r t, (Q * V)%M = M.
  Proof.
    intros. split; intros.
    - unfold lmis in H. destruct H as [H [H1 H2]]. repeat split; fin.
      + unfold vforall in H2. exists (lmis_eq_helper   H H1 H2).
        apply meq_iff_mnth. intros a b. unfold lmis_eq_helper.
        rewrite mnth_mmul. destruct (vmem_dec V (M a)) eqn : E.
        * destruct constructive_indefinite_description.
          rewrite <- e. unfold mvmul. rewrite !vdot_veye_l. auto.
        * destruct constructive_indefinite_description.
          rewrite lcomb_eq in e. rewrite <- e. unfold mvmul. auto.
    - destruct H as [H1 [H2 [Q H3]]]. unfold lmis. repeat split; auto.
      + unfold vforall. intros a; intro. apply lrep_iff_vconsT_ldep with (u:= (M a)) in H2.
        rewrite <- H2. unfold lrep. exists (Q a). rewrite lcomb_eq. rewrite <- H3.
        extensionality b. unfold mvmul. rewrite mnth_mmul. auto.
  Qed.

  
  Definition rank {n s} (M : @vec (@vec tA s) n) t : Prop :=
    exists vs : @vec (@vec tA s) t, lmis M vs.

  Lemma rank_row_0 :
    forall {n} (M : mat 0 n), rank M O.
  Proof.
    intros. unfold rank, lmis. exists (fun i : 'I_0 => vzero). repeat split.
    - unfold vmems, vforall. intro. pose proof (fin2nat_lt i); lia.
    - apply lindep_iff_coef0. intros. extensionality i. pose proof (fin2nat_lt i); lia.
    - unfold vforall, vexist. intro. pose proof (fin2nat_lt i); lia.
  Qed.

  Lemma rank_row_0_unique :
    forall {n t} (M : mat 0 n), rank M t -> t = O.
  Proof.
    intros. unfold rank in *. destruct H. unfold lmis in H.
    destruct H as [H _]. unfold vmems, vforall, vmem, vexist in H.
    destruct t; auto. specialize H with #0. destruct H. pose proof (fin2nat_lt x0); fin.
  Qed.

  Lemma rank_col_0 :
    forall {n} (M : mat n 0), rank M 0.
  Proof.
    intros. destruct n. apply rank_row_0.
     unfold rank, lmis. exists (fun i : 'I_0 => vzero). repeat split.
    - unfold vmems, vforall. intro. pose proof (fin2nat_lt i); lia.
    - apply lindep_iff_coef0. intros. extensionality i. pose proof (fin2nat_lt i); lia.
    - unfold vforall, vexist. intro. intros. apply ldep_if_contain_0. exists #0.
      unfold vconsT. destruct (#0 ??< O). auto. extensionality j. pose proof (fin2nat_lt j); lia.
  Qed.  

  Lemma rank_col_0_unique :
    forall {n t} (M : mat n 0), rank M t -> t = O.
  Proof.
    intros. unfold rank in *. destruct H. unfold lmis in H.
    destruct H as [_ [H _]]. destruct t; auto. exfalso. apply H.
    apply ldep_if_contain_0. exists #0. extensionality b.
     pose proof (fin2nat_lt b); fin.
  Qed.

  Lemma rank_mrowSwap :
    forall {n s} (M : mat n s) t i j,
      rank M t -> rank (mrowSwap i j M) t.
  Proof.
    intros. destruct H as [vs H]. destruct H as [H [H0 H1]].
    apply vmems_eq in H. destruct H as [P[H H2]]. unfold rank.
    exists (P * M)%M. unfold lmis. repeat split.
    - apply vmems_eq. exists (P * mrowSwapM i j)%M. split. 
      + rewrite mmul_assoc. f_equal. rewrite mrowSwap_eq.
        rewrite <- mmul_assoc. rewrite mmul_mrowSwapM_mrowSwapM.
        rewrite mmul_1_l; auto.
      + intros. rewrite mmul_mvmul. rename i0 into a.
        specialize H2 with a. destruct H2 as [k H2]. rewrite H2.
        assert ((exists j0 : 'I_n, forall b : 'I_n, mrowSwapM i j k b = veye j0 b) ->
          (exists j0 : 'I_n, veye k v* mrowSwapM i j = veye j0)).
        { intros. destruct H3 as [c H3]. exists c. extensionality b.
          unfold mvmul. rewrite vdot_veye_l. unfold mcol. apply H3. }
        apply H3. clear H3.
        destruct (k ??= i) as [E|E].
        1:{ eexists; intros; unfold mrowSwapM. destruct (k ??= i) as [E'|E'].
          instantiate (1:=j). unfold veye. 
          destruct (b ??= j); destruct (j ??= b); fin. fin. }
        destruct (k ??= j) as [E0|E0].
        1:{ eexists; intros; unfold mrowSwapM. destruct (k ??= i); try easy. 
            destruct (k ??= j) as [E0'|E0']. instantiate (1:=i). unfold veye. 
            destruct (b ??= i); destruct (i ??= b); fin. fin. }
        eexists; intros; unfold mrowSwapM. destruct (k ??= i); try easy.
        destruct (k ??= j); try easy.
    - rewrite H. auto.
    - unfold vforall in *. intros a. rewrite H. rewrite mrowSwap_vswap.
      unfold vswap. destruct (a ??= i) as [E|E].
      1:{ intros. apply H1; auto. } destruct (a ??= j) as [E'|E']. apply H1.
      apply H1.
  Qed.


  Definition rank_mrowScale_helper1 {t n} (cs : @vec tA t) (P : mat t n) (j : 'I_n) (k : tA)
    (E: forall i : 'I_t, exists j : 'I_n, P i = veye j) : @vec tA t.
  Proof.
    unfold vec; intro i. specialize E with i.
    apply constructive_indefinite_description in E. destruct E as [a H].
    destruct (a ??= j). exact (cs.[i] * k)%A. exact(cs.[i]).
  Defined.

  Definition rank_mrowScle_helper2 {t n} (cs : @vec tA t) (P : mat t n) (j : 'I_n) (k : tA)
    (E: forall i : 'I_t, exists j : 'I_n, P i = veye j) : @vec tA t.
  Proof.
    unfold vec; intro i. specialize E with i.
    apply constructive_indefinite_description in E. destruct E as [a H].
    destruct (a ??= j). exact (cs.[i] * (1 / k))%A. exact(cs.[i]).
  Defined.
 

  Lemma rank_mrowScale :
    forall {n s} (M : mat n s) t i k,
      k <> 0 -> rank M t -> rank (mrowScale i k M) t.
  Proof.
    intros n s M t i k Ek H. destruct H as [vs H]. destruct H as [H [H0 H1]].
    apply vmems_eq in H. destruct H as [P[H H2]]. unfold rank.
    exists (P * (mrowScaleM i k * M))%M. unfold lmis. repeat split.
    - apply vmems_eq. exists P. split. 
      + rewrite mrowScale_eq. auto.
      + apply H2.
    - unfold lindep in *. intro. apply H0. unfold ldep.
      unfold ldep in H3. destruct H3 as  [cs [H3 H4]].
      rewrite lcomb_eq in H4. assert (E:= H2). 
      exists (rank_mrowScale_helper1 cs  i k E)%M. split.
      + intro. apply H3. extensionality a.
        assert (rank_mrowScale_helper1 cs  i k E a= vzero a)%M. { rewrite H5. auto. }
        clear H5. unfold rank_mrowScale_helper1 in H6.
        destruct constructive_indefinite_description in H6. rename e into H5.
        unfold rank_mrowScale_helper1 in H5. rewrite vnth_vzero in *. destruct (x ??= i); auto.
        rewrite field_mul_eq0_iff in H6. destruct H6; fin. 
      + rewrite lcomb_eq. rewrite <- H4. unfold mvmul. extensionality a.
        rewrite <- H. unfold vdot. f_equal. extensionality b.
        rewrite !vnth_vmap2. unfold mcol. rewrite !mnth_mmul.
        unfold rank_mrowScale_helper1. destruct constructive_indefinite_description.
        destruct (x ??= i) as [E0|E0].
        * replace (cs b * k * (<P b,M&[a]>))%A with (cs b * (k * (<P b,M&[a]>)))%A by fin.
          f_equal. rewrite !e. rewrite !vdot_veye_l. rewrite <- mrowScale_eq.
          unfold mcol, mrowScale. destruct (x ??= i); fin.
        * f_equal. rewrite !e. rewrite !vdot_veye_l. rewrite <- mrowScale_eq.
          unfold mcol, mrowScale. destruct (x ??= i); fin.
    - unfold vforall in *. intros a. intros. rewrite <- H in H1.
      rewrite <- !mrowScale_eq in *.
      destruct (classic (vmem ((P * M)%M) (M a))) as [E|E].
      + rewrite !vmem_eq in E. destruct E as [p E]. specialize H2 with p. destruct H2 as [q H2].
        assert (a <> q). { intro; apply H3; subst. rewrite vmem_eq. exists p.
          extensionality b. unfold mvmul. rewrite vdot_veye_l. unfold mcol.
          rewrite mnth_mmul. rewrite H2. rewrite vdot_veye_l. unfold mcol. auto. }
        assert ((P * mrowScale i k M)%M.[p] = M a \/ (P * mrowScale i k M)%M.[p] = k s* M a). 
        { clear H3; unfold mrowScale in *. destruct (a ??= i) as [E1|E1]; destruct (q ??= i) as [E2|E2].
          * exfalso. apply H4. apply fin2nat_eq_iff. rewrite E1. rewrite E2. auto. 
          * left. extensionality b. rewrite mnth_mmul.
            assert ((veye p v* (P * M)%M) b =  ( M a b)%A) by (rewrite E; auto).
            unfold mvmul in H3. rewrite !vdot_veye_l in *. unfold mcol in *.
            rewrite !mnth_mmul in *. rewrite H2 in *. unfold mcol in *. rewrite !vdot_veye_l in *. 
            destruct (q??=i); fin.
          * right. extensionality b. assert ((veye p v* (P * M)%M) b =  (M a b)%A) by (rewrite E; auto).
            rewrite vnth_vscal. unfold mvmul in H3. rewrite !vdot_veye_l in *. unfold mcol in *.
            rewrite !mnth_mmul in *. rewrite H2 in *. unfold mcol in *. rewrite !vdot_veye_l in *. 
            destruct (q??=i); fin.
          * left. extensionality b. assert ((veye p v* (P * M)%M) b =  (M a b)%A) by (rewrite E; auto).
            unfold mvmul in H3. rewrite !vdot_veye_l in *. unfold mcol in *.
            rewrite !mnth_mmul in *. rewrite H2 in *. unfold mcol in *. rewrite !vdot_veye_l in *. 
            destruct (q??=i); fin. }
        rewrite ldep_iff_exist_lrep. exists (#t). unfold lrep.
        rewrite vnth_vconsT_n; fin. replace (vremove (vconsT (P * mrowScale i k M)%M (mrowScale i k M a)) #t) with
          (vremoveT (vconsT (P * mrowScale i k M)%M (mrowScale i k M a))).
        2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #t); fin.
            pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
            unfold mrowScale at 2. destruct H5; destruct (a ??= i) as [E'|E'].
        * exists (k s* veye p). rewrite lcomb_eq. extensionality b.
          unfold mvmul. rewrite vdot_vscal_l. rewrite vdot_veye_l.
          f_equal. unfold mcol. rewrite H5; auto.
        * exists (veye p). rewrite lcomb_eq. extensionality b.
          unfold mvmul. rewrite vdot_veye_l. unfold mcol. rewrite H5; auto.   
        * exists (veye p). rewrite lcomb_eq. extensionality b.
          destruct (a ??= i); fin. unfold mvmul. rewrite vdot_veye_l. unfold mcol.
          rewrite H5. rewrite vnth_vscal. auto.
        * exists ((1/k) s* veye p). rewrite lcomb_eq. extensionality b.
          destruct (a ??= i); fin. unfold mvmul. rewrite vdot_vscal_l. rewrite vdot_veye_l. unfold mcol.
          rewrite H5. rewrite vnth_vscal. replace (1 / k * (k * M a b))%A with ((1 / k * k * M a b)%A) by fin.
          apply field_mulInvL_inv1 in Ek. rewrite Ek. fin.
      + apply H1 in E. rewrite <- H in H0. apply ldep_vconsT_lindep_imply_lrep in E; auto.
        unfold lrep in E. destruct E as [cs E]. rewrite lcomb_eq in E.
        rewrite ldep_iff_exist_lrep. exists #t. unfold lrep.
        rewrite vnth_vconsT_n; fin. replace (vremove (vconsT (P * mrowScale i k M)%M (mrowScale i k M a)) #t) with
          (vremoveT (vconsT (P * mrowScale i k M)%M (mrowScale i k M a))).
        2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #t); fin.
            pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT. 
            unfold mrowScale at 2. assert (E0 := H2). destruct (a ??= i) as [E'|E'].
        * exists (k s* (rank_mrowScle_helper2 cs i k E0)). rewrite lcomb_eq.
          rewrite <- E. extensionality b. unfold mvmul. rewrite vdot_vscal_l. f_equal.
          unfold mcol, vdot. f_equal. extensionality c. rewrite !vnth_vmap2.
          unfold rank_mrowScle_helper2. destruct constructive_indefinite_description.
          rewrite !mnth_mmul. rewrite e. rewrite !vdot_veye_l. unfold mcol.
          unfold mrowScale. destruct (x ??= i); fin.
          replace (cs c * (1 / k) * (k * M x b))%A with
            (cs c * (((1 / k) * k) * M x b))%A by fin. f_equal.
          apply field_mulInvL_inv1 in Ek. rewrite Ek. fin.
        * exists ((rank_mrowScle_helper2 cs i k E0)). rewrite lcomb_eq.
          rewrite <- E. extensionality b. unfold mvmul.
          unfold mcol, vdot. f_equal. extensionality c. rewrite !vnth_vmap2.
          unfold rank_mrowScle_helper2. destruct constructive_indefinite_description.
          rewrite !mnth_mmul. rewrite e. rewrite !vdot_veye_l. unfold mcol.
          unfold mrowScale. destruct (x ??= i); fin.
          replace (cs c * (1 / k) * (k * M x b))%A with
            (cs c * (((1 / k) * k) * M x b))%A by fin. f_equal.
          apply field_mulInvL_inv1 in Ek. rewrite Ek. fin.
  Qed.


  Definition rank_mrowAdd_helper1 {t n} (cs : @vec tA t) (P : mat t n) (k : 'I_n) (j : 'I_t) (c : tA)
    (E: forall i : 'I_t, exists j : 'I_n, P i = veye j) : @vec tA t.
  Proof.
    unfold vec; intro i. specialize E with i.
    apply constructive_indefinite_description in E. destruct E as [a H].
    destruct (a ??= k). exact (cs.[i] * c)%A. exact(cs.[i]).
  Defined.

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

  Lemma rank_mrowAdd :
    forall {n s} (M : mat n s) t i j k,
      i <> j -> rank M t -> rank (mrowAdd i j k M) t.
  Proof.
    intros n s M t i j k Eij H. destruct H as [vs H]. destruct H as [H [H0 H1]].
    apply vmems_lindep_infer in H; auto. destruct H as [P[H [H2 H3]]]. unfold rank.
    assert (H4 := H3). specialize H4 with i. 
    assert (H5 := H3). specialize H5 with j. 
    destruct H4 as [[p H4] | H4].  destruct H5 as [[q H5] | H5].
    - assert (P.[p] = veye i). { specialize H2 with p. destruct H2 as [o H2].
        assert (P&[i] p = veye p p) by (rewrite H4; auto). unfold mcol, veye in H6.
        destruct (p ??= p); fin. assert (P p i = veye o i) by (rewrite H2; auto).
        rewrite H6 in H7; unfold veye in H7. destruct (o ??= i) as [E|E].
        - apply fin2nat_eq_iff in E; subst o. auto.
        - pose proof field_1_neq_0. contradiction. }
      assert (P.[q] = veye j). { specialize H2 with q. destruct H2 as [o H2].
        assert (P&[j] q = veye q q) by (rewrite H5; auto). unfold mcol, veye in H7.
        destruct (q ??= q); fin. assert (P q j = veye o j) by (rewrite H2; auto).
        rewrite H7 in H8; unfold veye in H8. destruct (o ??= j) as [E|E].
        - apply fin2nat_eq_iff in E; subst o. auto.
        - pose proof field_1_neq_0. contradiction. }
      assert (Epq : p <> q). { intro. subst. rewrite H6 in H7.
        rewrite veye_eq in H7. contradiction. apply field_1_neq_0. }
      exists (P * (mrowAdd i j k  M))%M. unfold lmis. repeat split.
      + apply vmems_eq. exists P. split; auto.
      + apply lindep_iff_coef0. intros. rewrite lcomb_eq in H8.
        rewrite <- H in *. rewrite lindep_iff_coef0 in H0.
        specialize H0 with (vadd cs ((k * cs.[p])%A s* (veye q))).
        assert (lcomb (cs + (k * cs.[p])%A s* veye q) (P * M)%M = vzero).
        { rewrite lcomb_eq. rewrite <- H8. extensionality b.
          unfold mvmul. rewrite vdot_vadd_l. rewrite mrowAdd_madd.
          rewrite mmul_madd_distr_l. rewrite mcol_madd.
          rewrite vdot_vadd_r. f_equal. rewrite !mcol_mmul.
          replace ((fun i0 : 'I_n => if i0 ??= i then k s* M j else vzero)&[b])
            with ((k * M.[j].[b])%A s* (veye i)).
          2:{ extensionality d. rewrite vnth_vscal. unfold mcol.
              unfold veye. destruct (i ??= d); destruct (d ??= i); fin.
              - rewrite vnth_vscal. fin.
              - rewrite vnth_vzero. fin. }
          rewrite vdot_vscal_l. rewrite vdot_veye_l.
          unfold mmulv at 1. rewrite H7. rewrite vdot_veye_l. unfold mcol.
          rewrite mmulv_vscal. rewrite vdot_vscal_r. 
          replace ((k * cs p * M j b)%A) with ((k * M j b * cs p)%A) by fin.
          f_equal. replace (P *v veye i) with P&[i]. rewrite H4. rewrite vdot_veye_r.
          auto. extensionality c. unfold mmulv. rewrite vdot_veye_r. auto. }
        apply H0 in H9. assert (cs = ((- k * cs p)%A s* veye q)).
        { extensionality c. assert ((cs + (k * cs p)%A s* veye q) c = vzero c) by (rewrite H9; auto).
          rewrite vnth_vadd in H10. rewrite !vnth_vscal in *. rewrite vnth_vzero in *.
          unfold veye in *. destruct (q ??= c). apply group_opp_uniq_r in H10. rewrite <- H10; fin.
          apply group_opp_uniq_r in H10. rewrite <- H10; fin. } 
      extensionality b. clear H8. assert ((cs + (k * cs p)%A s* veye q) p = vzero p) by (rewrite H9; fin).
      rewrite vnth_vzero in H8. rewrite vnth_vadd in H8. rewrite vnth_vscal in H8.
      replace (veye q p) with 0 in H8. 2: { unfold veye. destruct (q ??= p); fin. }
      replace (cs p + k * cs p * 0)%A with (cs p) in H8 by fin. rewrite vnth_vzero.
      rewrite H10. rewrite vnth_vscal. rewrite H8. fin.
      + unfold vforall in *. intros a. intros. rewrite <- H in *.
        destruct (classic (vmem (P*M)%M (M a))) as [E|E].
        * rewrite !vmem_eq in E. destruct E as [x E]. specialize H2 with x. destruct H2 as [y H2].
        assert (a <> y). { intro; apply H8; subst. rewrite vmem_eq. exists x.
          extensionality b. unfold mvmul. rewrite vdot_veye_l. unfold mcol.
          rewrite mnth_mmul. rewrite H2. rewrite vdot_veye_l. unfold mcol. auto. }
        assert ((P * mrowAdd i j k M)%M.[x] = M a \/ (P * mrowAdd i j k M)%M.[x] = M a + k s* (P * mrowAdd i j k M)%M.[q]). 
        { clear H8; unfold mrowAdd in *. destruct (a ??= i) as [E1|E1]; destruct (y ??= i) as [E2|E2].
          * exfalso. apply H9. apply fin2nat_eq_iff. rewrite E1. rewrite E2. auto. 
          * left. extensionality b. rewrite mnth_mmul.
            assert ((veye x v* (P * M)%M) b =  (M a b)%A) by (rewrite E; auto).
            unfold mvmul in H8. rewrite !vdot_veye_l in *. unfold mcol in *.
            rewrite !mnth_mmul in *. rewrite H2 in *. unfold mcol in *. rewrite !vdot_veye_l in *. 
            destruct (y??=i); fin.
          * right. extensionality b. assert ((veye x v* (P * M)%M) b =  (M a b)%A) by (rewrite E; auto).
            rewrite vnth_vadd. rewrite vnth_vscal. unfold mvmul in H8. rewrite !vdot_veye_l in *. unfold mcol in *.
            rewrite !mnth_mmul in *. rewrite H2 in *. unfold mcol in *. rewrite !vdot_veye_l in *.
            rewrite H7. rewrite vdot_veye_l. destruct (y??=i); fin. f_equal; fin.
          * left. extensionality b. assert ((veye x v* (P * M)%M) b =  (M a b)%A) by (rewrite E; auto).
            unfold mvmul in H8. rewrite !vdot_veye_l in *. unfold mcol in *.
            rewrite !mnth_mmul in *. rewrite H2 in *. unfold mcol in *. rewrite !vdot_veye_l in *. 
            destruct (y??=i); fin. }
        rewrite ldep_iff_exist_lrep. exists (#t). unfold lrep.
        rewrite vnth_vconsT_n; fin. replace (vremove (vconsT (P * mrowAdd i j k M)%M (mrowAdd i j k M a)) #t) with
          (vremoveT (vconsT (P * mrowAdd i j k M)%M (mrowAdd i j k M a))).
        2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #t); fin.
            pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
            unfold mrowAdd at 2. destruct H10; destruct (a ??= i) as [E'|E'].
          ** exists (veye x + (k s* veye q)). rewrite lcomb_eq. extensionality b.
            unfold mvmul. rewrite vdot_vadd_l. rewrite vdot_vscal_l. rewrite !vdot_veye_l.
            f_equal; unfold mcol. rewrite H10; auto. f_equal. rewrite mnth_mmul.
            rewrite  H7. rewrite vdot_veye_l. unfold mcol, mrowAdd. destruct (j ??= i); fin.
          ** exists (veye x). rewrite lcomb_eq. extensionality b.
            unfold mvmul. rewrite !vdot_veye_l.
            f_equal; unfold mcol. rewrite H10; auto.
          ** exists (veye x). rewrite lcomb_eq. extensionality b.
            unfold mvmul. rewrite !vdot_veye_l.
            unfold mcol. rewrite H10; auto. f_equal. rewrite vnth_vadd. f_equal.
            rewrite vnth_vscal. f_equal. rewrite mnth_mmul. rewrite H7.
            rewrite vdot_veye_l. unfold mcol, mrowAdd. destruct (j ??= i); fin.
          ** exists (veye x + (- k s* veye q)). rewrite lcomb_eq. extensionality b.
            unfold mvmul. rewrite vdot_vadd_l. rewrite vdot_vscal_l. rewrite !vdot_veye_l.
            unfold mcol; rewrite H10. rewrite vnth_vadd. 
            replace (M a b + (k s* (P * mrowAdd i j k M)%M q) b + - k * (P * mrowAdd i j k M)%M q b)%A 
            with (M a b + ((k s* (P * mrowAdd i j k M)%M q) b + - k * (P * mrowAdd i j k M)%M q b))%A by fin.
            replace ((k s* (P * mrowAdd i j k M)%M q) b + - k * (P * mrowAdd i j k M)%M q b)%A with 0.
            fin. symmetry. rewrite vnth_vscal. fin.
        * apply H1 in E. apply ldep_vconsT_lindep_imply_lrep in E; auto.
          unfold lrep in E. destruct E as [cs E]. rewrite lcomb_eq in E.
          rewrite ldep_iff_exist_lrep. exists #t. unfold lrep.
          rewrite vnth_vconsT_n; fin. replace (vremove (vconsT (P * mrowAdd i j k M)%M (mrowAdd i j k M a)) #t) with
          (vremoveT (vconsT (P * mrowAdd i j k M)%M (mrowAdd i j k M a))).
          2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #t); fin.
            pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT. 
            unfold mrowAdd at 2. assert (E0 := H2). destruct (a ??= i) as [E'|E'].
          ** rewrite fin2nat_eq_iff in E'. subst.
            replace (fun j0 : 'I_s => (M i j0 + k * M j j0)%A) with (M i + k s* M j).
            2:{ extensionality c. rewrite vnth_vadd. rewrite vnth_vscal. auto. }
            exists (cs + ((k - (k * cs.[p])%A)%A s* veye q)). rewrite lcomb_eq.
            extensionality b. rewrite vnth_mvmul. rewrite vdot_vadd_l.
            rewrite mcol_mmul. replace ((<cs,P *v (mrowAdd i j k M)&[b]>)) with
              (M i b + k * cs p * M j b)%A.
            2: { symmetry. assert ((cs v* (P * M)%M) b = M i b) by (rewrite E; auto).
                rewrite vnth_mvmul in H. rewrite mrowAdd_madd. rewrite mcol_madd.
                rewrite mmulv_vadd. rewrite vdot_vadd_r. rewrite mcol_mmul in H.
                rewrite H. f_equal. 
                replace ((fun i0 : 'I_n => if i0 ??= i then k s* M j
                  else vzero)&[b]) with ((k * M j b) s* (veye i))%A.
                rewrite mmulv_vscal. rewrite vdot_vscal_r.
                replace ((k * cs p * M j b)%A) with ((k * M j b * cs p)%A) by fin.
                f_equal. unfold mmulv. replace (fun i0 : 'I_t => <P i0,veye i>) with (P&[i]).
                rewrite H4. rewrite vdot_veye_r; auto. extensionality c. rewrite vdot_veye_r. auto.
                extensionality c. unfold mcol. rewrite vnth_vscal. unfold veye.
                destruct (i ??= c); destruct (c ??= i); fin. rewrite vnth_vscal. fin.
                rewrite vnth_vzero. fin. }
            rewrite vdot_vscal_l. rewrite vdot_veye_l. rewrite vnth_mmulv. rewrite H7.
            rewrite vdot_veye_l. unfold mcol. unfold mrowAdd. destruct (j ??= i); fin.
            rewrite vnth_vadd. rewrite vnth_vscal. fin.
          ** replace (fun j0 : 'I_s => M a j0) with (M a).
            2:{ extensionality c. auto. }
            exists (cs + ((- (k * cs.[p])%A) s* veye q)). rewrite lcomb_eq.
            extensionality b. rewrite vnth_mvmul. rewrite vdot_vadd_l.
            rewrite mcol_mmul. replace ((<cs,P *v (mrowAdd i j k M)&[b]>)) with
              (M a b + k * cs p * M j b)%A.
            2: { symmetry. assert ((cs v* (P * M)%M) b = M a b) by (rewrite E; auto).
                rewrite vnth_mvmul in H9. rewrite mrowAdd_madd. rewrite mcol_madd.
                rewrite mmulv_vadd. rewrite vdot_vadd_r. rewrite mcol_mmul in H9.
                rewrite H9. f_equal. 
                replace ((fun i0 : 'I_n => if i0 ??= i then k s* M j
                  else vzero)&[b]) with ((k * M j b) s* (veye i))%A.
                rewrite mmulv_vscal. rewrite vdot_vscal_r.
                replace ((k * cs p * M j b)%A) with ((k * M j b * cs p)%A) by fin.
                f_equal. unfold mmulv. replace (fun i0 : 'I_t => <P i0,veye i>) with (P&[i]).
                rewrite H4. rewrite vdot_veye_r; auto. extensionality c. rewrite vdot_veye_r. auto.
                extensionality c. unfold mcol. rewrite vnth_vscal. unfold veye.
                destruct (i ??= c); destruct (c ??= i); fin. rewrite vnth_vscal. fin.
                rewrite vnth_vzero. fin. }
            rewrite vdot_vscal_l. rewrite vdot_veye_l. rewrite vnth_mmulv. rewrite H7.
            rewrite vdot_veye_l. unfold mcol. unfold mrowAdd. destruct (j ??= i); fin.
    - assert (P.[p] = veye i). { specialize H2 with p. destruct H2 as [o H2].
        assert (P&[i] p = veye p p) by (rewrite H4; auto). unfold mcol, veye in H6.
        destruct (p ??= p); fin. assert (P p i = veye o i) by (rewrite H2; auto).
        rewrite H6 in H7; unfold veye in H7. destruct (o ??= i) as [E|E].
        - apply fin2nat_eq_iff in E; subst o. auto.
        - pose proof field_1_neq_0. contradiction. }
      destruct (classic (k = 0))%A.
      1:{ exists vs. replace (mrowAdd i j k M) with M. unfold lmis; repeat split; auto.
          rewrite vmems_eq. exists P; split; auto. apply meq_iff_mnth. intros a b.
          unfold mrowAdd. rewrite H7. destruct (a ??= i); fin. } rename H7 into Ek.
    destruct (ldep_or_lindep (P * (mrowAdd i j k M))%M).
      + exists ((fun i' : 'I_t => if i' ??= p then veye j else P.[i']) * (mrowAdd i j k  M))%M.
        destruct t. 1:{ pose proof (fin2nat_lt p); lia. }
        assert (lindep (vremove vs p)).
        { destruct t. 
            1:{ unfold lindep; intro. unfold ldep in H8. destruct H8 as [cs' [H8 H9]].
                apply H8.  extensionality b. pose proof (fin2nat_lt b); lia. }
          apply lindep_iff_coef0. intros cs; intros. rewrite lindep_iff_coef0 in H0.
          specialize H0 with (vinsert cs p 0). assert (lcomb (vinsert cs p 0) vs = vzero).
          { rewrite lcomb_coef_vinsert_0. auto. }
          apply H0 in H9. extensionality b. rewrite vnth_vzero. destruct (b ??< p) as [E|E].
          - assert (vinsert cs p 0 (fSuccRange b) = vzero (fSuccRange b)) by (rewrite H9; auto).
            rewrite vnth_vzero in H10. erewrite vnth_vinsert_lt in H10. rewrite <- H10; fin.
          - assert (vinsert cs p 0 (fSuccRangeS b) = vzero (fSuccRangeS b)) by (rewrite H9; auto).
            assert (p < (fSuccRangeS b)) by fin.  rewrite vnth_vzero in H10.
            erewrite vnth_vinsert_gt in H10. rewrite <- H10; fin. apply H11. }
        assert (P * mrowAdd i j k M = vinsert (vremove vs p) p (M i + k s* M j))%M.
          { erewrite vinsert_vremove_eq. Unshelve. all:fin. apply meq_iff_mnth. 
            intros a b. unfold vset. destruct (a ??= p) as [E|E].
            - apply fin2nat_eq_iff in E; subst. rewrite mnth_mmul. 
              rewrite H6. rewrite vdot_veye_l. unfold mcol, mrowAdd.
              destruct (i ??= i); fin.
            - rewrite <- H. rewrite !mnth_mmul. specialize H2 with a. destruct H2 as [x H2].
              rewrite H2. rewrite !vdot_veye_l. unfold mcol.
              unfold mrowAdd. destruct (x ??= i) as [E'|E']; auto.
              apply fin2nat_eq_iff in E'; subst. exfalso; apply E. clear E. 
              assert (P a i = 1). { rewrite H2. unfold veye; destruct (i ??= i); fin. }
              assert (P&[i] a = veye p a) by (rewrite H4; auto). unfold mcol in H9. 
              rewrite H in H9. unfold veye in H9. destruct (p ??= a); fin.
              pose proof field_1_neq_0. contradiction. }
        assert ((fun i' : 'I_(S t) => if i' ??= p then veye j else P i') *
            mrowAdd i j k M  = (vinsert (vremove vs p) p (M j)))%M.
        { erewrite vinsert_vremove_eq. Unshelve. all:fin. apply meq_iff_mnth.
               intros a b. unfold vset. destruct (a ??= p) as [E|E].
            - apply fin2nat_eq_iff in E; subst. rewrite mnth_mmul. destruct (p??=p); fin. 
              rewrite vdot_veye_l. unfold mcol, mrowAdd. destruct (j??=i); fin.
            - rewrite <- H. rewrite !mnth_mmul. specialize H2 with a. destruct H2 as [x H2].
              destruct (a??=p). 1:{ fin. } clear n0. rewrite H2. rewrite !vdot_veye_l. unfold mcol.
              unfold mrowAdd. destruct (x ??= i) as [E'|E']; auto.
              apply fin2nat_eq_iff in E'; subst. exfalso; apply E. clear E. 
              assert (P a i = 1). { rewrite H2. unfold veye; destruct (i ??= i); fin. }
              assert (P&[i] a = veye p a) by (rewrite H4; auto). unfold mcol in H10. 
              rewrite H in H10. unfold veye in H10. destruct (p ??= a); fin.
              pose proof field_1_neq_0. contradiction. }
          assert (P * M = vinsert (vremove vs p) p (M i))%M.
          { erewrite vinsert_vremove_eq. Unshelve. all:fin. apply meq_iff_mnth. 
            intros a b. unfold vset. destruct (a ??= p) as [E|E].
            - apply fin2nat_eq_iff in E; subst. rewrite mnth_mmul. 
              rewrite H6. rewrite vdot_veye_l. unfold mcol, mrowAdd.
              destruct (i ??= i); fin.
            - rewrite <- H. rewrite !mnth_mmul. specialize H2 with a. destruct H2 as [x H2].
              rewrite H2. rewrite !vdot_veye_l. unfold mcol.
              unfold mrowAdd. destruct (x ??= i) as [E'|E']; auto. }
        rewrite H10. rewrite <- H in *. assert (Evs:= H0). rewrite H11 in H0. rewrite H9 in H7.
        assert (lindep (vinsert (vremove (P * M)%M p) p (k s* M j))).
          {  apply lindep_insert_ldep_lindep in H7; auto. }
        unfold lmis; repeat split.
        * rewrite <- H10. rewrite vmems_eq. exists (fun i' : 'I_(S t) => if i' ??= p then veye j else P i').
          split; auto. intros a. destruct (a ??= p). exists j; auto.
          specialize H2 with a. destruct H2 as [b H2]. exists b. apply H2; auto.
        * erewrite vinsert_vremove_eq in *. Unshelve. 2: fin.
          apply lindep_subst with (cs:= (/k) s* veye p) (i:=p) in H12. 
          replace (vset (P * M)%M p (M j)) with (vset (vset (P * M)%M p (k s* M j)) p
          (lcomb (/ k s* veye p) (vset (P * M)%M p (k s* M j)%M))). apply H12.
          rewrite H. extensionality x. extensionality y.
          unfold vset. destruct (x ??= p).
          ** rewrite lcomb_eq. unfold mvmul. rewrite vdot_vscal_l.
            rewrite vdot_veye_l. unfold mcol. destruct (p ??= p); fin.
            rewrite vnth_vscal. rewrite <- associative. rewrite field_mulInvL.
            rewrite field_mul_1_l; auto. auto.
          ** auto.
          ** rewrite vnth_vscal. unfold veye. destruct (p ??= p); fin.
            rewrite field_mul_1_r. rewrite field_inv_neq0_iff. auto.
      * unfold vforall in *. intros a. intro. clear H10.
        destruct (classic (vmem ((P * M)%M) (M a))) as [E|E];destruct (a ??= i).
        ** rewrite fin2nat_eq_iff in e; subst. rewrite ldep_iff_exist_lrep.
          exists #(S t). rewrite remove_removeT. rewrite vremoveT_vconsT.
          rewrite vnth_vconsT_n; fin. apply ldep_vinsert_lindep_imply_lrep in H7. all : fin.
          unfold mrowAdd. destruct (i??=i); fin. clear e.
          replace ((fun j0 : 'I_s => (M i j0 + k * M j j0)%A)) with (M i + k s* M j).
          2:{ extensionality b. fin. } unfold lrep. unfold lrep in H7. destruct H7 as [cs H7].
          exists (vinsert cs p 0). rewrite lcomb_coef_vinsert. rewrite vscal_0_l.
          erewrite vremove_vinsert. rewrite vadd_0_r. auto. Unshelve. all : fin.
        **  rewrite fin2nat_neq_iff in n0.
          unfold mrowAdd in *. destruct (a ??= i); fin. clear n1.
          replace (fun j : 'I_s => M a j) with (M a) in *. 2:{ extensionality b. fin. }
          destruct (classic (M a = M i)).
          *** subst. rewrite ldep_iff_exist_lrep.
          exists #(S t). rewrite remove_removeT. rewrite vremoveT_vconsT.
          rewrite vnth_vconsT_n; fin. apply ldep_vinsert_lindep_imply_lrep in H7. all : fin.
          unfold mrowAdd. destruct (i??=i); fin. clear e. rewrite H10.
          unfold lrep. unfold lrep in H7. destruct H7 as [cs H7].
          exists (vinsert cs p (-k)). rewrite lcomb_coef_vinsert. rewrite lcomb_eq in *.
          erewrite vremove_vinsert. Unshelve. 2: fin. rewrite H7. extensionality x.
          rewrite !vnth_vadd. rewrite !vnth_vscal.
          replace (- k * vinsert (vremove (P * M)%M p) p (M j) p x)%A 
            with (- (k * vinsert (vremove (P * M)%M p) p (M j) p x))%A by fin.
          rewrite field_sub_add. f_equal. f_equal. erewrite vinsert_vremove_eq.
          Unshelve. 2: fin. unfold vset. destruct (p ??= p); fin; auto.
          *** rewrite vmem_eq in E. destruct E as [q E]. assert (q <> p).
            { intro. subst. apply H10. extensionality b.
              assert ((veye p v* (P * M)%M) b = M a b) by (rewrite E; auto).
              rewrite vnth_mvmul in H. rewrite vdot_veye_l in H. unfold mcol in H.
              rewrite mnth_mmul in H. rewrite H6 in H. rewrite vdot_veye_l in H. rewrite <-  H. auto. }
          clear H9. exfalso. apply H13. erewrite vinsert_vremove_eq.
          Unshelve. 2: fin. rewrite vmem_eq.
          exists q. rewrite <- E. unfold mvmul. extensionality x. rewrite !vdot_veye_l.
          unfold mcol. unfold vset. destruct (q ??= p); fin.
        ** apply fin2nat_eq_iff in e; subst. unfold mrowAdd.
          destruct (i ??= i ); fin.
          replace (fun j0 : 'I_s => (M i j0 + k * M j j0)%A) with (M i + k s* M j).
          2:{ extensionality x. fin. }
          apply lrep_iff_vinsert_ldep with (v:=M i + k s* M j) (i:=p) in H8.
          rewrite <- H8 in H7. rewrite ldep_iff_exist_lrep. exists (#(S t)).
          rewrite remove_removeT. rewrite vremoveT_vconsT. rewrite vnth_vconsT_n.
          2: fin. destruct H7 as [cs H7]. unfold lrep. exists (vinsert cs p 0).
          rewrite lcomb_coef_vinsert. rewrite vscal_0_l.
          erewrite vremove_vinsert. rewrite vadd_0_r. apply H7. Unshelve. fin.
        ** unfold mrowAdd in *. destruct (a ??= i); fin. clear n0.
           replace ((fun j : 'I_s => M a j)) with (M a) in * by fin.
          rewrite ldep_iff_exist_lrep. exists (#(S t)).
          rewrite remove_removeT. rewrite vremoveT_vconsT. rewrite vnth_vconsT_n.
          2: fin. unfold lrep. clear H9. apply H1 in E. eapply lrep_iff_vconsT_ldep in Evs.
          rewrite <- Evs in E. clear Evs. unfold lrep in E. destruct E as [cs1 E]. 
          apply lrep_iff_vinsert_ldep with (v:=M i + k s* M j) (i:=p) in H8.
          rewrite <- H8 in H7. unfold lrep in H7. destruct H7 as [cs2 H7].
          exists (cs1 + (cs1.[p] s* (vinsert cs2 p 0)) + (((- (k+1)) * cs1 p)%A s* (veye p))%V).
          rewrite !lcomb_eq in *. extensionality x.
          assert (A0 : (cs1 v* (P * M)%M) x = M a x) by (rewrite E; auto).
          assert (A1 : (cs2 v* vremove (P * M)%M p) x = (M i + k s* M j) x) by (rewrite H7; auto).
          unfold mvmul in *. rewrite vnth_vadd in A1. rewrite vnth_vscal in A1.
          rewrite !vdot_vadd_l. rewrite !vdot_vscal_l. rewrite vdot_veye_l.
          unfold mvmul in *. rewrite !vinsert_mcol. rewrite !vremove_mcol in *.
          rewrite !vdot_vinsert_r. erewrite !vnth_vinsert_eq.
          erewrite vremove_vinsert. 
          replace ((<cs2,vremove (P * M)%M&[x] p>) + M j x * 0)%A
            with (<cs2,vremove (P * M)%M&[x] p>) by fin. rewrite A1.
          rewrite vdot_vremove. rewrite A0. unfold mcol. rewrite mnth_mmul.
          rewrite H6; rewrite vdot_veye_l. unfold mcol. fin.
          Unshelve. all : fin.
    + exists (P * (mrowAdd i j k  M))%M. 
      destruct t. 1:{ pose proof (fin2nat_lt p); lia. }
      assert (P * mrowAdd i j k M = vinsert (vremove vs p) p (M i + k s* M j))%M.
          { erewrite vinsert_vremove_eq. Unshelve. all:fin. apply meq_iff_mnth. 
            intros a b. unfold vset. destruct (a ??= p) as [E|E].
            - apply fin2nat_eq_iff in E; subst. rewrite mnth_mmul. 
              rewrite H6. rewrite vdot_veye_l. unfold mcol, mrowAdd.
              destruct (i ??= i); fin.
            - rewrite <- H. rewrite !mnth_mmul. specialize H2 with a. destruct H2 as [x H2].
              rewrite H2. rewrite !vdot_veye_l. unfold mcol.
              unfold mrowAdd. destruct (x ??= i) as [E'|E']; auto.
              apply fin2nat_eq_iff in E'; subst. exfalso; apply E. clear E. 
              assert (P a i = 1). { rewrite H2. unfold veye; destruct (i ??= i); fin. }
              assert (P&[i] a = veye p a) by (rewrite H4; auto). unfold mcol in H8. 
              rewrite H in H8. unfold veye in H8. destruct (p ??= a); fin.
              pose proof field_1_neq_0. contradiction. }
          assert (P * M = vinsert (vremove vs p) p (M i))%M.
          { erewrite vinsert_vremove_eq. Unshelve. all:fin. apply meq_iff_mnth. 
            intros a b. unfold vset. destruct (a ??= p) as [E|E].
            - apply fin2nat_eq_iff in E; subst. rewrite mnth_mmul. 
              rewrite H6. rewrite vdot_veye_l. unfold mcol, mrowAdd.
              destruct (i ??= i); fin.
            - rewrite <- H. rewrite !mnth_mmul. specialize H2 with a. destruct H2 as [x H2].
              rewrite H2. rewrite !vdot_veye_l. unfold mcol.
              unfold mrowAdd. destruct (x ??= i) as [E'|E']; auto. }
        unfold lmis; repeat split.
      * rewrite vmems_eq. exists P; split; auto.
      * auto.
      * unfold vforall in *. intros a. intros. rewrite <- H in *.
        destruct (a ??= i) as [E|E].
        { apply fin2nat_eq_iff in E; subst.
          replace (mrowAdd i j k M i) with (M i + (k s* M j)%A) in *.
          exfalso. apply H10. exists p. rewrite H8.
          erewrite vinsert_vremove_eq. unfold vset. destruct (p??=p); fin.
          extensionality b. unfold mrowAdd. destruct (i??=i); fin. } 
        { replace (mrowAdd i j k M a) with (M a) in *.
          destruct (classic (vmem (P * M)%M M.[a])).
          - destruct (classic (M a = M i)).
            + rewrite H12 in *. destruct (classic (vmem (P * M)%M (M j))).
              * apply vmem_eq in H13. destruct H13 as [q H13]. destruct (classic (p = q)).
                { subst. assert (M i = M j).
                  { rewrite <- H13. extensionality b. unfold mvmul. rewrite vdot_veye_l.
                    unfold mcol; rewrite mnth_mmul. rewrite H6. rewrite vdot_veye_l. auto. } 
                  rewrite <- H in *; auto. rewrite ldep_iff_exist_lrep. exists (#(S t)). rewrite vnth_vconsT_n; fin.
                  unfold lrep. exists (/ (1 + k)%A s* veye q)%V.
                  replace (vremove (vconsT (P * mrowAdd i j k M)%M (M i)) #(S t)) with
                  (vremoveT (vconsT (P * mrowAdd i j k M)%M (M i))).
                  2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #(S t)); fin.
                  pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
                  erewrite vinsert_vremove_eq in *. rewrite H8. rewrite lcomb_eq.
                  extensionality x. unfold mvmul. rewrite vdot_vscal_l. rewrite vdot_veye_l.
                  unfold mcol, vset. destruct (q ??= q); fin. rewrite vnth_vadd. rewrite vnth_vscal.
                  replace (M i x + k * M i x)%A with ((1 + k)%A * M i x)%A by fin.
                  rewrite <- associative. destruct (classic (1+k=0)%A).
                  - exfalso. apply lindep_then_all_not0 with (i:=q) in H7. apply H7.
                    rewrite H8. unfold vset. destruct (q ??= q); fin.
                    extensionality b. rewrite vnth_vzero. rewrite vnth_vadd.
                    rewrite vnth_vscal. replace (M i b + k * M i b)%A with ((1 + k)%A * M i b)%A by fin.
                    rewrite H14. fin.
                  - rewrite field_mulInvL; fin.
                  Unshelve. all : fin. } 
                { rewrite ldep_iff_exist_lrep. exists (#(S t)). rewrite vnth_vconsT_n; fin.
                  unfold lrep. exists (veye p + ((- k) s* veye q))%V.
                  replace (vremove (vconsT (P * mrowAdd i j k M)%M (M i)) #(S t)) with
                  (vremoveT (vconsT (P * mrowAdd i j k M)%M (M i))).
                  2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #(S t)); fin.
                  pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
                  erewrite vinsert_vremove_eq in *. rewrite H8. rewrite lcomb_eq.
                  extensionality x. unfold mvmul. rewrite vdot_vadd_l. rewrite vdot_vscal_l. rewrite !vdot_veye_l.
                  unfold mcol, vset. destruct (p??= p); [|fin]. destruct (q ??= p);[fin|].
                  replace ((P * M)%M q x) with (M j x).
                  2:{ rewrite <- H13. unfold mvmul. rewrite vdot_veye_l. auto. }
                  rewrite vnth_vadd. rewrite vnth_vscal. fin. }
              * apply H1 in H13. apply lrep_iff_vconsT_ldep with (u:=(M j)) in H0. erewrite vinsert_vremove_eq in *.
                rewrite <- H0 in H13. rewrite ldep_iff_exist_lrep. exists (#(S t)). rewrite vnth_vconsT_n; fin.
                unfold lrep. destruct H13 as [cs H13]. 
                assert (lcomb cs (vset (P * M)%M p (M i + k s* M j)) = (1 + k * cs.[p])%A s* M j).
                { extensionality b. rewrite vnth_vscal.
                  replace ((1 + k * cs p) * M j b)%A with (M j b + k * cs p * M j b)%A by fin.
                  replace (M j b) with (lcomb cs (P * M)%M b) at 1 by (rewrite H13; fin).
                  rewrite !lcomb_eq. unfold mvmul. rewrite vset_mcol.
                  rewrite vdot_vset_r. rewrite vdot_vremove. rewrite !associative. f_equal.
                  rewrite vnth_vadd. rewrite vnth_vscal. 
                  replace ((M i b + k * M j b) * cs p)%A with (cs p* M i b + k * cs p *  M j b)%A by fin.
                  replace ((P * M)%M&[b] p) with (M i b). fin. unfold mcol. rewrite mnth_mmul.
                  rewrite H6; rewrite vdot_veye_l; fin. Unshelve. all: fin.
                }
                destruct (classic ((1 + k * cs.[p])%A = 0)).
                { rewrite H15 in H14.
                  assert (lcomb cs (vset (P * M)%M p (M i + k s* M j)) = vzero).
                  { rewrite H14. extensionality b. rewrite vnth_vscal.
                    rewrite vnth_vzero. fin. } clear H14.
                  exfalso. apply H7. rewrite <- H8 in H16. unfold ldep.
                  exists cs; split; auto. intro. rewrite H14 in H15.
                  rewrite vnth_vzero in H15. pose proof field_1_neq_0. apply H17.
                  replace (1 + k * 0)%A with 1 in H15 by fin. auto. }
                { exists (veye p + (-(k * (/ (1 + k * cs.[p]))))%A s* cs).
                  replace (vremove (vconsT (P * mrowAdd i j k M)%M (M i)) #(S t)) with
                  (vremoveT (vconsT (P * mrowAdd i j k M)%M (M i))).
                  2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #(S t)); fin.
                  pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
                  rewrite lcomb_eq. extensionality x. unfold mvmul. rewrite vdot_vadd_l.
                  replace (<veye p,(P * mrowAdd i j k M)%M&[x]>) with (M i x + k * M j x)%A.
                  rewrite vdot_vscal_l.
                  replace (<cs,(P * mrowAdd i j k M)%M&[x]>)%A with ((1 + k * cs.[p])%A * M j x)%A.
                  rewrite <- !associative. replace (M i x) with (M i x + 0)%A at 2 by fin.
                  replace (M i x + k * M j x + - (k / (1 + k * cs p)) * (1 + k * cs p) * M j x)%A with
                    (M i x + (k * M j x + - (k / (1 + k * cs p)) * (1 + k * cs p) * M j x))%A by fin.
                  f_equal. replace (- (k / (1 + k * cs p)) * (1 + k * cs p))%A with (- k); fin.
                  replace (- (k / (1 + k * cs p)) * (1 + k * cs p))%A with (-((k / (1 + k * cs p)) * (1 + k * cs p)))%A by fin.
                  replace ((Amul (Amul k (Ainv (Aadd Aone (Amul k (cs p))))) (Aadd Aone (Amul k (cs p))))) with
                    (k * ((/ (1 + k * cs p)) * (1 + k * cs p)))%A by fin.
                  replace (/ (1 + k * cs p) * (1 + k * cs p))%A with 1. fin.
                  rewrite field_mulInvL; fin.
                  - rewrite H8. replace ((1 + k * cs p) * M j x)%A with (((1 + k * cs.[p])%A s* M j) x).
                    rewrite <- H14. rewrite lcomb_eq. auto. rewrite vnth_vscal. auto.
                  - rewrite vdot_veye_l. unfold mcol. rewrite mnth_mmul. rewrite H6.
                    rewrite vdot_veye_l. unfold mcol. unfold mrowAdd. destruct (i??=i); fin.
                  }
              + exfalso. apply H10. rewrite vmem_eq in *. destruct H11 as [x H11].
                destruct (classic (x = p)).
                * subst. exfalso. apply H12. rewrite <- H11. extensionality y.
                  unfold mvmul. rewrite vdot_veye_l. unfold mcol. rewrite mnth_mmul.
                  rewrite H6. rewrite vdot_veye_l. auto.
                * exists x. rewrite <- H11. rewrite  H8. erewrite vinsert_vremove_eq. 
                  unfold mvmul. extensionality y. rewrite !vdot_veye_l. unfold mcol.
                  unfold vset. destruct (x ??= p); fin. Unshelve. all : fin.
            - apply H1 in H11. apply lrep_iff_vconsT_ldep with (u:=(M a)) in H0 as H0'.
              rewrite <- H0' in H11. destruct H11 as [cs H11].
              destruct (classic (vmem (P * M)%M (M j))).
              * apply vmem_eq in H12. destruct H12 as [q H13]. destruct (classic (p = q)).
                { subst. assert (M i = M j).
                  { rewrite <- H13. extensionality b. unfold mvmul. rewrite vdot_veye_l.
                    unfold mcol; rewrite mnth_mmul. rewrite H6. rewrite vdot_veye_l. auto. } 
                  rewrite <- H in *; auto. rewrite ldep_iff_exist_lrep. exists (#(S t)). rewrite vnth_vconsT_n; fin.
                  unfold lrep. exists (vset cs q (cs q / (1 + k))%A)%V.
                  replace (vremove (vconsT (P * mrowAdd i j k M)%M (M a)) #(S t)) with
                  (vremoveT (vconsT (P * mrowAdd i j k M)%M (M a))).
                  2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #(S t)); fin.
                  pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
                  erewrite vinsert_vremove_eq in *. rewrite H8. rewrite lcomb_eq.
                  extensionality x. unfold mvmul. rewrite vset_mcol. rewrite vdot_vset.
                  replace (<cs,(P * M)%M&[x]>) with (M a x). replace ((P * M)%M&[x] q) with (M i x).
                  rewrite !associative. replace (M a x)%A with (M a x + 0)%A  at 2 by fin. fin.
                  replace ((- (cs q * M i x) + cs q * (/ (1 + k) * (M i + k s* M i)%V x)))%A 
                    with (cs q * (/ (1 + k) * (M i + k s* M i)%V x) - (cs q * M i x))%A by fin.
                  rewrite field_sub_add. replace ((0 + cs q * M i x)%A) with (cs q * M i x)%A by fin. fin.
                  rewrite vnth_vadd. rewrite vnth_vscal.
                  replace (M i x + k * M i x)%A with ((1 + k) * (M i x))%A by fin.
                  replace (/ (1 + k) * ((1 + k) * M i x))%A with ((/ (1 + k) * (1 + k)) * M i x)%A by fin.
                  destruct (classic (1+k=0)%A).
                  - exfalso. apply lindep_then_all_not0 with (i:=q) in H7. apply H7.
                    rewrite H8. unfold vset. destruct (q ??= q); fin.
                    extensionality b. rewrite vnth_vzero. rewrite vnth_vadd.
                    rewrite vnth_vscal. replace (M i b + k * M i b)%A with ((1 + k)%A * M i b)%A by fin.
                    rewrite H12. fin. Unshelve. all : fin. 
                  - rewrite field_mulInvL; fin.
                  - unfold mcol. rewrite mnth_mmul. rewrite H6. rewrite vdot_veye_l. auto.
                  - rewrite <- H11. rewrite lcomb_eq. auto. } 
                { rewrite ldep_iff_exist_lrep. exists (#(S t)). rewrite vnth_vconsT_n; fin.
                  unfold lrep. exists (cs + ((- (k * cs.[p]))%A s* veye q))%V.
                  replace (vremove (vconsT (P * mrowAdd i j k M)%M (M a)) #(S t)) with
                  (vremoveT (vconsT (P * mrowAdd i j k M)%M (M a))).
                  2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #(S t)); fin.
                  pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
                  erewrite vinsert_vremove_eq in *. rewrite H8. rewrite lcomb_eq.
                  extensionality x. unfold mvmul. rewrite !vdot_vadd_l. rewrite !vdot_vscal_l.
                  rewrite !vdot_veye_l. replace ((<cs,(vset (P * M)%M p (M i + k s* M j)%V)&[x]>))%A with
                    (M a x + k * cs.[p] * M j x)%A. unfold mcol, vset.
                  destruct (q ??= p);[fin|]. replace ((P * M)%M q x)%A with (M j x). fin.
                  - rewrite <- H13. unfold mvmul. rewrite vdot_veye_l. auto.
                  - rewrite vset_mcol. rewrite vdot_vset_r. rewrite vdot_vremove.
                    replace (<cs,(P * M)%M&[x]>) with (M a x). rewrite vnth_vadd. rewrite vnth_vscal.
                    replace ((P * M)%M&[x] p) with (M i x). fin.
                    + unfold mcol. rewrite mnth_mmul. rewrite H6. rewrite vdot_veye_l. auto.
                    + rewrite <- H11. rewrite lcomb_eq. unfold mvmul. auto.
                    Unshelve. all : fin. }
              * apply H1 in H12. apply lrep_iff_vconsT_ldep with (u:=(M j)) in H0.
                rewrite <- H0 in H12. destruct H12 as [cs' H12]. rewrite lcomb_eq in *.
                erewrite vinsert_vremove_eq in *. Unshelve. all : fin.
                assert (cs' v* (P * mrowAdd i j k M)%M = (1 + (k * cs'.[p]))%A s* M j)%V.
                { extensionality x. rewrite vnth_vscal.
                  replace ((1 - k * cs' p) * M j x)%A with ( M j x - k * cs' p *  M j x)%A by fin.
                  rewrite H8. unfold mvmul. rewrite vset_mcol. rewrite vdot_vset_r.
                  rewrite vdot_vremove. replace ((<cs',(P * M)%M&[x]>))%A with (M j x).
                  replace ((P * M)%M&[x] p)%A with (M i x). rewrite vnth_vadd. rewrite vnth_vscal.
                  replace ((M i x + k * M j x) * cs' p)%A with (cs' p * M i x + k * cs' p * M j x)%A by fin.
                  fin.
                  - unfold mcol. rewrite mnth_mmul. rewrite H6; rewrite vdot_veye_l. auto.
                  - rewrite <- H12. auto.  
                }
                assert ((1 + k * cs'.[p])%A <> 0).
                { intro. rewrite H14 in H13. apply H7. unfold ldep. exists cs'; split.
                  - intro. rewrite H15 in H14. rewrite vnth_vzero in H14.
                    pose proof field_1_neq_0. apply H16. rewrite <- H14. fin.
                  - rewrite lcomb_eq. rewrite H13. extensionality b. rewrite vnth_vzero.
                    rewrite vnth_vscal. fin. }
                assert (M a = (cs v* (P * mrowAdd i j k M)%M)%V + (- (k * cs.[p]))%A s* M j)%V.
                { extensionality x. rewrite vnth_vadd. rewrite vnth_vscal.
                  rewrite H8. unfold mvmul. rewrite vset_mcol. rewrite vdot_vset_r.
                  rewrite vdot_vremove. replace (<cs,(P * M)%M&[x]>) with (M a x).
                  replace (M a x) with (M a x + 0)%A at 1 by fin. rewrite !associative.
                  f_equal. symmetry. rewrite vnth_vadd. rewrite vnth_vscal.
                  rewrite <- !associative. replace ((P * M)%M&[x] p) with (M i x).
                  replace ((M i x + k * M j x) * cs p)%A with (cs p * M i x + k * cs p * M j x)%A by fin.
                  fin.
                  - unfold mcol. rewrite mnth_mmul. rewrite H6; rewrite vdot_veye_l. auto.
                  - rewrite <- H11. auto. }
                rewrite ldep_iff_exist_lrep. exists (#(S t)). rewrite vnth_vconsT_n; fin.
                unfold lrep. exists (cs + ((- (k * cs.[p] / (1 + k * cs'.[p])))%A s* cs'))%V.
                replace (vremove (vconsT (P * mrowAdd i j k M)%M (M a)) #(S t)) with
                  (vremoveT (vconsT (P * mrowAdd i j k M)%M (M a))).
                2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #(S t)); fin.
                  pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT.
                rewrite lcomb_eq. rewrite H15. extensionality x. rewrite vnth_vadd.
                unfold mvmul. rewrite vdot_vadd_l. f_equal. rewrite vdot_vscal_l.
                rewrite vnth_vscal. replace (<cs',(P * mrowAdd i j k M)%M&[x]>)%A with
                  (((1 + k * cs'.[p])%A s* M j) x). rewrite vnth_vscal.
                replace (- (k * cs p / (1 + k * cs' p)) * ((1 + k * cs' p) * M j x))%A with
                  (- (k * cs p  * ((/ (1 + k * cs' p)) * ((1 + k * cs' p)) * M j x)))%A by fin.
                replace (- (k * cs p) * M j x)%A with (- ((k * cs p) * M j x))%A by fin.
                f_equal. f_equal. replace (/ (1 + k * cs' p) * (1 + k * cs' p))%A with 1. fin.
                symmetry. rewrite field_mulInvL; fin. rewrite <- H13. unfold mvmul. auto.
            - extensionality x. unfold mrowAdd. destruct (a??=i); fin. }
    - clear H5. assert (P * ((mrowAdd i j k M)) = vs)%M.
      { apply meq_iff_mnth. intros a b. rewrite <- H.
        rewrite !mnth_mmul. specialize H2 with a. destruct H2 as [c H2].
        rewrite H2. rewrite !vdot_veye_l. unfold mcol. unfold mrowAdd.
        destruct (c ??= i) as [E|E]; fin. exfalso. apply fin2nat_eq_iff in E; subst.
        assert (P a i = 1). { rewrite H2. unfold veye. destruct (i??=i); fin. }
        assert (P&[i] a = vzero a) by (rewrite H4; auto). rewrite vnth_vzero in H5.
        unfold mcol in H5. pose proof field_1_neq_0. apply H6. rewrite <- H; rewrite H5; auto. }
       exists vs. unfold lmis; repeat split.
      + rewrite vmems_eq. exists P. split; auto.
      + auto.
      + unfold vforall in *. intros a. intro.
        apply lrep_iff_vconsT_ldep with (u:=(mrowAdd i j k M a)) in H0 as H7.
        rewrite <- H7. clear H7. unfold lrep.
        assert (Ea : a <> i -> mrowAdd i j k M a = M a).
        { intros. extensionality b. unfold mrowAdd. destruct (a ??= i); fin. }     
        destruct (classic (a = i)); [| rewrite (Ea H7) in *; clear Ea];
        destruct (classic (vmem vs (M a))); destruct (classic (vmem vs (M j))).
        * subst. clear H6. rewrite vmem_eq in *. destruct H9 as [p H9].
          destruct H8 as [q H8]. exists (veye q + k s* veye p).
          rewrite lcomb_eq. extensionality x. unfold mvmul.
          rewrite vdot_vadd_l. rewrite vdot_vscal_l. unfold mrowAdd.
          destruct (i ??= i); fin. f_equal.
          { rewrite <- H8. unfold mvmul. auto. }
          { f_equal. rewrite <- H9. unfold mvmul. auto. }
        * subst. apply H1 in H9. apply lrep_iff_vconsT_ldep with (u:= M j) in H0.
          rewrite <- H0 in H9. destruct H9 as [cs H9]. clear H6. rewrite vmem_eq in H8.
          destruct H8 as [p H8]. exists (veye p  + k s* cs). rewrite lcomb_eq in *.
          extensionality x. unfold mvmul, mrowAdd. destruct (i ??= i); fin.
          rewrite vdot_vadd_l. rewrite vdot_vscal_l. f_equal.
          rewrite <- H8. unfold mvmul. auto.
          f_equal. rewrite <- H9. auto.
        * subst. apply H1 in H8. apply lrep_iff_vconsT_ldep with (u:= M i) in H0.
          rewrite <- H0 in H8. destruct H8 as [cs H8]. clear H6. rewrite vmem_eq in H9.
          destruct H9 as [p H9]. exists (cs  + k s* veye p). rewrite lcomb_eq in *.
          extensionality x. unfold mvmul, mrowAdd. destruct (i ??= i); fin.
          rewrite vdot_vadd_l. rewrite vdot_vscal_l. f_equal.
          rewrite <- H8. unfold mvmul. auto.
          f_equal. rewrite <- H9. auto.
        * subst. apply H1 in H8. apply lrep_iff_vconsT_ldep with (u:= M i) in H0 as H0'.
          rewrite <- H0' in H8. destruct H8 as [cs H8].
          apply H1 in H9. apply lrep_iff_vconsT_ldep with (u:= M j) in H0.
          rewrite <- H0 in H9. destruct H9 as [cs' H9].
          exists (cs  + k s* cs'). rewrite lcomb_eq in *.
          extensionality x. unfold mvmul, mrowAdd. destruct (i ??= i); fin.
          rewrite vdot_vadd_l. rewrite vdot_vscal_l. f_equal.
          rewrite <- H8. unfold mvmul. auto.
          f_equal. rewrite <- H9. auto.
        * exfalso. apply H6; auto.
        * exfalso. apply H6; auto.
        * clear H8. apply H1 in H6. apply lrep_iff_vconsT_ldep with (u:= M a) in H0 as H0'.
          rewrite <- H0' in H6. destruct H6 as [cs H6]. exists cs. auto.
        * clear H8. apply H1 in H6. apply lrep_iff_vconsT_ldep with (u:= M a) in H0 as H0'.
          rewrite <- H0' in H6. destruct H6 as [cs H6]. exists cs. auto.
  Qed.
  
  Theorem MRT_keep_ldep : forall {n s} (M N : mat (S n) s),
    MRT M N -> ldep M -> ldep N.
  Proof.
    intros. induction H.
    - unfold ldep in *. destruct H0 as [cs [H0 H1]].
      exists (vswap cs i j). split.
      + apply vneq_vzero. apply vneq_vzero in H0. destruct H0 as [a H0].
        destruct (j ??= a); [|destruct (i ??= a)].
        * apply fin2nat_eq_iff in e; subst. exists i. unfold vswap.
          destruct  (i ??= i); fin.
        * apply fin2nat_eq_iff in e; subst. exists j.  unfold vswap.
          destruct  (j ??= j); fin.
        * exists a. unfold vswap. fin.
      + rewrite !lcomb_eq. rewrite <- H1. rewrite lcomb_eq.
        extensionality b. unfold mvmul.
        replace ((mrowSwap i j M)&[b]) with (vswap (M&[b]) i j).
        rewrite vdot_vswap; fin.
        extensionality p. unfold vswap, mrowSwap, mcol. auto.
    - unfold ldep in *. destruct H0 as [cs [H0 H1]].
      exists (vscale cs i (/K)). split.
      + apply vneq_vzero. apply vneq_vzero in H0. destruct H0 as [a H0].
        exists a. unfold vscale in *. destruct (a ??= i); fin.
        rewrite fin2nat_eq_iff in e; subst. apply field_mul_neq0_iff. split; auto.
        apply field_inv_neq0_if_neq0; fin.
      + rewrite !lcomb_eq. rewrite <- H1. rewrite lcomb_eq.
        extensionality b. unfold mvmul.
        replace (vscale cs i (/ K)) with (vset cs i (cs.[i] * (/ K))).
        replace ((mrowScale i K M)&[b]) with (vset (M&[b]) i (K * M i b)).
        rewrite vdot_vset. replace (cs i / K * (K * M i b)) with (cs i * M&[b] i).
        fin. replace (cs i / K * (K * M i b)) with (cs i * (/ K * K * M i b)) by fin.
        f_equal. replace (/ K * K) with 1. unfold mcol; fin. symmetry. apply field_mulInvL; auto.
        extensionality p. unfold vset, mrowScale, mcol. auto. destruct (p ??= i); fin.
        apply fin2nat_eq_iff in e; subst; auto.
        extensionality p. unfold vscale, vset, mcol. auto. destruct (p ??= i); fin.
    - apply ldep_iff_exist_lrep in H0. destruct H0 as [a H0]; auto.
      apply ldep_iff_exist_lrep. exists a. destruct (a ??= i); [|destruct (a ??= j)].
      + apply fin2nat_eq_iff in e; subst.
        replace (vremove (mrowAdd i j K M) i) with (vremove M i).
        replace (mrowAdd i j K M i) with (M i + K s* M j).
        unfold lrep in *. destruct H0 as [cs H0].
        exists (vremove (vinsert cs i 0 + K s* veye j) i).
        replace (M i) with (lcomb cs (vremove M i)) at 1.
        rewrite !lcomb_eq in *. extensionality p. rewrite vnth_vadd.
        rewrite vnth_vscal. unfold mvmul. rewrite vremove_mcol.
        rewrite vdot_vremove. rewrite vdot_vadd_l. rewrite vdot_vscal_l.
        rewrite vdot_vinsert_l. rewrite vdot_veye_l. rewrite !vnth_vadd.
        erewrite !vnth_vinsert_eq. rewrite vnth_vscal. unfold veye.
        destruct (j ??= i); fin. replace ((0 + K * 0) * M&[p] i)%A with 0 by fin.
        replace (0 * M&[p] i) with 0 by fin. unfold mcol. fin.
        extensionality p. rewrite vnth_vadd; rewrite vnth_vscal. unfold mrowAdd.
        destruct (i??=i); fin.
        apply meq_iff_mnth. intros a b. unfold vremove, mrowAdd.
        destruct (a??<i).
        destruct (fSuccRange a ??= i). exfalso. fin. auto.
        destruct (fSuccRangeS a ??= i). exfalso. fin. auto. Unshelve. fin.
      + shelve. 
      + replace (mrowAdd i j K M a) with (M a).
        unfold lrep in *. destruct H0 as [cs H0]. rewrite lcomb_eq in H0.
        assert (forall b, <vinsert cs a 0, (mrowAdd i j K M)&[b]> = (M a b) + K * (vinsert cs a 0 i) * M j b)%A.
        { intros. rewrite <- H0. unfold mvmul. 
          replace ((mrowAdd i j K M)&[b]) with (M&[b] + K * M j b s* veye i).
          rewrite vremove_mcol. rewrite vdot_vadd_r. rewrite vdot_vscal_r.
          rewrite vdot_veye_r. rewrite vdot_vinsert_0_l. fin.
          extensionality p. rewrite vnth_vadd. rewrite vnth_vscal.
          unfold mrowAdd, mcol, veye. destruct (i ??= p); destruct (p??=i); fin. }
        exists (vremove (vinsert cs a 0 + (- K * (vinsert cs a 0).[i])%A s* veye j) a)%M.
        rewrite lcomb_eq in *. extensionality b. unfold mvmul.
        rewrite vremove_mcol. rewrite vdot_vremove.
        replace ((mrowAdd i j K M)&[b] a) with (M a b). rewrite !vdot_vadd_l.
        rewrite H1. rewrite vdot_vscal_l. rewrite vdot_veye_l.
        replace ((mrowAdd i j K M)&[b] j) with (M j b).
        rewrite vnth_vadd. rewrite vnth_vscal. erewrite !vnth_vinsert_eq.
        unfold veye. destruct (j ??= a); fin. unfold mrowAdd, mcol.
        destruct (j ??= i); fin. unfold mrowAdd, mcol. destruct (a??=i); fin.
        extensionality b. unfold mrowAdd, mcol. destruct (a??=i); fin.
    - auto.
    -apply IHMRT2. apply IHMRT1. apply H0.
  Admitted.  

  Lemma lindep_row_gt_col: forall n t (P : mat (S n) (S t)), 
    n > t -> ldep P.
  Proof.
    intros. destruct (existisRREFbyMRT P) as [N [H0 H1]].
    apply MRT_keep_ldep with N. apply MRTsym. auto.  
    apply getPivotNum_col_lt_row in H1; fin. apply ldep_if_contain_0.
    exists #n. auto.
  Qed.
    
  Lemma lreps_more_imply_ldep : forall {s n t} (vs : @vec (@vec tA (S s)) (S n)) (us : @vec (@vec tA (S s)) (S t)),
    lreps us vs -> n > t -> ldep vs.
  Proof.
  intros s n t vs us Hrep Hnt. apply lreps_eq in Hrep as H. destruct H as [P H].
  assert (ldep P). apply lindep_row_gt_col. fin. unfold ldep in H0.
  destruct H0 as [c [H1 H2]]. exists c. split.
  - assumption.  (* c <> vzero *)
  - rewrite !lcomb_eq in *. rewrite <- H. rewrite mvmul_assoc. 
    rewrite H2. extensionality x. unfold mvmul. rewrite vnth_vzero. rewrite vdot_0_l. auto.
  Qed.

  Lemma lindep_vsequiv :
    forall {t s n} (vs : @vec (vec (S n)) t) (us : @vec (vec (S n)) s),
      lindep vs -> lindep us-> vsequiv vs us ->
      t = s.
  Proof. 
    intros. destruct H1. destruct t; [|destruct s].
    - rewrite lreps_eq in H1. destruct H1 as [Q H1]. rewrite mmul_0 in H1.
      rewrite <- H1 in H0. destruct s; fin. exfalso; apply H0. apply ldep_if_contain_0.
      exists #0. extensionality i. rewrite vnth_vzero. unfold mat0. auto.
    - rewrite lreps_eq in H2. destruct H2 as [Q H2]. rewrite mmul_0 in H2.
      rewrite <- H2 in H. exfalso; apply H. apply ldep_if_contain_0.
      exists #0. extensionality i. rewrite vnth_vzero. unfold mat0. auto.
    - destruct (lt_eq_lt_dec t s) as [[E|E]|E]; auto; exfalso.
      + apply H0. apply lreps_more_imply_ldep with (vs); fin.
      + apply H. apply lreps_more_imply_ldep with (us); fin.
  Qed.
    
  Lemma rank_unique : forall {s n t1 t2} (M : mat s n),
    rank M t1 -> rank M t2 -> t1 = t2.
  Proof.
    intros.  destruct s;[|destruct n].
    - assert (t1 = O). { apply rank_row_0_unique with M. auto. }
      assert (t2 = O). { apply rank_row_0_unique with M. auto. }
      rewrite H1; rewrite H2; auto.
    - assert (t1 = O). { apply rank_col_0_unique with M. auto. }
      assert (t2 = O). { apply rank_col_0_unique with M. auto. }
      rewrite H1; rewrite H2; auto.
    - intros. unfold rank in *. destruct H as [vs H]. destruct H0 as [us H0].
      pose proof (@lindep_vsequiv _ _ _ vs us). apply H1.
      + destruct H as [_ [H _]]. auto.
      + destruct H0 as [_ [H0 _]]. auto.
      + apply lmis_vsequiv_any with M; auto.
  Qed.

  Lemma MRT_rank': forall {n s t} (M M' : mat n s),
    MRT M M' -> rank M t -> rank M' t.
  Proof.
    intros. induction H.
    - apply rank_mrowSwap; auto.
    - apply rank_mrowScale; auto.
    - apply rank_mrowAdd; auto.
    - auto.
    - auto.
  Qed.

  Theorem MRT_rank: forall {n s} (M M' : mat (S n) (S s)),
    MRT M M' -> (forall t, rank M t <-> rank M' t).
  Proof.
    intros; split; intros. apply MRT_rank' with M; fin.
    apply MRT_rank' with M'; fin. apply MRTsym; auto.
  Qed.

  Notation isRREF := (@isRREF _ Azero Aone _).

  Lemma isRREF_rank :
    forall {n s} (M: mat (S n) (S s)),
    isRREF M -> rank M (getPivotNum M (S n)).
  Proof.
    intros. unfold rank. exists ((fun a => M.[#a]) : mat (getPivotNum M (S n)) (S s)). 
    unfold lmis. repeat split.
    - rewrite vmems_eq. exists (fun i => veye #(fin2nat i)). repeat split.
      + apply meq_iff_mnth. intros x y. rewrite mnth_mmul. rewrite vdot_veye_l. auto.
      + intros. exists (#(fin2nat i)). auto.
    - destruct (getPivotNum M (S n)) as [|n'] eqn : E.
      + unfold lindep, ldep. intro. destruct H0 as [cs [H0 H1]]. apply H0. extensionality a.
        pose proof (fin2nat_lt a); lia.
      + apply lindep_iff_none_lrep. intros. intro. destruct H0 as [cs H0]. rewrite lcomb_eq in H0.
        pose proof (@getPivotNum_prop _ Azero Aone _  n s M n' i).
        destruct H1; fin. destruct H1. rename x into j.
        assert ((cs v* vremove (fun a : 'I_(S n') => M #a) i) j = M #i j) by (rewrite H0; fin).
        replace cs with (vremove (vinsert cs i 0) i) in H3.
        2 : { erewrite vremove_vinsert; auto. Unshelve. fin. }
        unfold mvmul in H3. rewrite vremove_mcol in H3. rewrite vdot_vremove in H3.
        rewrite H2 in H3. rewrite vdot_veye_r in H3. unfold veye in H3.
        destruct (i??=i); fin. replace (vinsert cs i 0 i - (vinsert cs i 0 i * 1)%A)%A with 0 in H3 by fin .
        symmetry in H3. apply getrowPivot_imply_nonzero in H1. apply H1; apply H3; auto.
    - destruct (getPivotNum M (S n)) as [|n'] eqn : E.
      + unfold vforall; intros a. intro. apply ldep_if_contain_0. exists (#(getPivotNum M (S n))).
        rewrite vnth_vconsT_n; fin. apply getPivotNum_None with (getPivotNum M (S n)); fin.
        destruct H. fin.
      + unfold vforall. intros a. intro. destruct (S n' ??<= a).
        * apply ldep_if_contain_0. exists (#(S n')).
        rewrite vnth_vconsT_n; fin. apply getPivotNum_None with (getPivotNum M (S n)); fin.
        destruct H. fin.
        * exfalso. apply H0. apply vmem_eq. exists #a. extensionality b. 
          unfold mvmul. rewrite vdot_veye_l. unfold mcol. fin.
  Qed.

  Lemma rank_exist : forall {n s} (M: mat n s),
    exists t, rank M t.
  Proof.
    destruct n;[|destruct s]; intros.
    - exists O. apply rank_row_0.
    - exists O. apply rank_col_0. 
    - intros. pose proof (existisRREFbyMRT M). destruct H as [N [H H0]].
      apply isRREF_rank in H0. exists (getPivotNum N (S n)). 
      apply MRT_rank with (t:=(getPivotNum N (S n))) in H . rewrite H; auto.
  Qed.

  Definition lrank {n s} (M : @vec (@vec tA s) n) t : Prop :=
    exists vs : @vec (@vec tA n) t, lmis (mtrans M) vs.

  Lemma lrank_mtrans : 
    forall {n s t} (M : @vec (@vec tA s) n),
    lrank M t = rank (mtrans M) t.
  Proof.
    intros. unfold rank, lrank. auto.
  Qed.

  Lemma lrank_unique : forall {s n t1 t2} (M : mat s n),
    lrank M t1 -> lrank M t2 -> t1 = t2.
  Proof.
    intros.  destruct s;[|destruct n].
    - rewrite !lrank_mtrans in *.
      assert (t1 = O). { apply rank_col_0_unique with (M\T). auto. }
      assert (t2 = O). { apply rank_col_0_unique with (M\T). auto. }
      rewrite H1; rewrite H2; auto.
    - rewrite !lrank_mtrans in *.
      assert (t1 = O). { apply rank_row_0_unique with (M\T). auto. }
      assert (t2 = O). { apply rank_row_0_unique with (M\T). auto. }
      rewrite H1; rewrite H2; auto.
    - rewrite !lrank_mtrans in *. apply rank_unique with (M\T); auto.
  Qed.

  Theorem MRT_lrank' : forall {n s t} (M M' : mat n s),
    MRT M M' -> lrank M t -> lrank M' t.
  Proof.
  Admitted.


  Lemma MRT_lrank: forall {n s} (M M' : mat (S n) (S s)),
    MRT M M' -> (forall t, lrank M t <-> lrank M' t).
  Proof.
    intros; split; intros. apply MRT_lrank' with M; fin.
    apply MRT_lrank' with M'; fin. apply MRTsym; auto.
  Qed.
    
  Notation getPivotNum_prop := (@getPivotNum_prop _ Azero Aone _ _ _).
  Notation getPivotNum_exists_veye := (@getPivotNum_exists_veye _ Azero Aone _ _ _).

  Lemma isRREF_lrank :
    forall {n s} (M: mat (S n) (S s)),
    isRREF M -> lrank M (getPivotNum M (S n)).
  Proof.
    intros. rewrite lrank_mtrans. unfold rank. unfold lrank.
    assert (En: getPivotNum M (S n) <= S n). {apply getPivotNum_le. }
    assert (H' := H). exists ((fun i => veye #i)). unfold lmis. repeat split.
    - unfold vmems, vforall. intro i. unfold vmem, vexist.
      pose proof (getPivotNum_exists_veye M #i). apply H0 in H.
      2:{ pose proof (fin2nat_lt  i). rewrite fin2nat_nat2finS; fin. }
      clear H0. destruct H as [j H]. exists j. rewrite <- H.
      unfold mcol, mtrans; auto.
    - apply lindep_iff_coef0. intros. rewrite lcomb_eq in H0.
      extensionality x. assert  ((cs v* (fun i : 'I_(getPivotNum M (S n)) => veye (#i : 'I_(S n)))) #x = 
        vzero (#x : 'I_(S n))) by (rewrite H0; auto). rewrite vnth_vzero in *.
      unfold mvmul in H1. unfold mcol in H1. 
      replace (fun i : fin (@MatrixGauss.getPivotNum tA Azero AeqDec n s M (S n)) =>
      @Vector.veye tA Azero Aone (S n) (@nat2finS n (@fin2nat (@MatrixGauss.getPivotNum tA Azero AeqDec n s M (S n)) i))
      (@nat2finS n (@fin2nat (@MatrixGauss.getPivotNum tA Azero AeqDec n s M (S n)) x))) with (veye x) in H1.
      rewrite vdot_veye_r in H1. auto. extensionality y. unfold veye.
      rewrite !fin2nat_nat2finS. destruct (x ??= y); destruct (y ??= x); fin.
      pose proof (fin2nat_lt x); fin. pose proof (fin2nat_lt y); fin.
    - unfold vforall. intros a; intro. apply ldep_iff_exist_lrep.
      exists (#(getPivotNum M (S n))). rewrite vnth_vconsT_n; fin.
      replace (vremove (vconsT (fun i : 'I_(getPivotNum M (S n)) => veye #i) ((M\T) a)) #(getPivotNum M (S n))) with
        (vremoveT (vconsT (fun i : 'I_(getPivotNum M (S n)) => veye #i) ((M\T) a))).
      2:{ unfold vremoveT, vremove. extensionality b. destruct (b ??< #(getPivotNum M (S n))); fin.
      pose proof (fin2nat_lt b). lia. } rewrite vremoveT_vconsT. unfold lrep.
      exists (fun b : 'I_(getPivotNum M (S n)) => (M\T) a #b). rewrite lcomb_eq.
      extensionality b. unfold mvmul. unfold mcol.
      destruct (getPivotNum M (S n)) as [|n'] eqn : E.
      * rewrite vdot_0. unfold mtrans; symmetry.
        apply getPivotNum_None with (i:=b) in E; fin. rewrite E. rewrite vnth_vzero. auto.
        destruct H; fin.
      * destruct (classic (b <= n')).
        ** replace (fun i : fin (S n') => @Vector.veye tA Azero Aone (S n) (@nat2finS n (@fin2nat (S n') i)) b) with 
            (veye (@nat2finS n' b)). rewrite vdot_veye_r.
          pose proof (fin2nat_lt b). f_equal; fin. extensionality i. unfold veye.
          rewrite !fin2nat_nat2finS. destruct (b ??= i); destruct (i ??= b); fin.
          pose proof (fin2nat_lt i); lia. lia.
        ** replace (fun i : fin (S n') => @Vector.veye tA Azero Aone (S n) (@nat2finS n (@fin2nat (S n') i)) b) with 
            (@Vector.vzero _ Azero (S n')).
          2: { extensionality y. rewrite vnth_vzero. unfold veye. destruct (#y ??= b); auto.
               pose proof (fin2nat_lt y). rewrite fin2nat_nat2finS in e; fin. }
          rewrite vdot_0_r. symmetry. unfold mtrans. apply getPivotNum_None with (i:= b) in E; fin.
          rewrite E. rewrite vnth_vzero; auto. destruct H; auto.
  Qed.

  Lemma rank_lrank : forall {n s t} (M: mat n s),
    rank M t <-> lrank M t.
  Proof.
    intros. destruct n; [|destruct s].
    - split; intros.
      + assert (t = O). { apply rank_row_0_unique with M. auto. }
        rewrite H0. rewrite lrank_mtrans. apply rank_col_0.
      + rewrite lrank_mtrans in H. assert (t = O). { apply rank_col_0_unique with (M\T). auto. }
        rewrite H0. apply rank_row_0.
    - split; intros.
      + assert (t = O). { apply rank_col_0_unique with M. auto. }
        rewrite H0. rewrite lrank_mtrans. apply rank_row_0.
      + rewrite lrank_mtrans in H. assert (t = O). { apply rank_row_0_unique with (M\T). auto. }
        rewrite H0. apply rank_col_0.
    - pose proof (existisRREFbyMRT M).
      destruct H as [N [H0 H1]]. apply isRREF_rank in H1 as H2.
      apply isRREF_lrank in H1 as H3. split; intros.
      + assert (t =(getPivotNum N (S n))).
        { apply rank_unique with N; auto. apply MRT_rank with (t:=t) in H0.
        rewrite <- H0. auto. } subst.
        apply MRT_lrank with (t:=(getPivotNum N (S n))) in H0. rewrite H0. auto.
      + assert (t =(getPivotNum N (S n))).
      { apply lrank_unique with N; auto. apply MRT_lrank with (t:=t) in H0.
        rewrite <- H0. auto. } subst.
        apply MRT_rank with (t:=(getPivotNum N (S n))) in H0. rewrite H0. auto.
  Qed.

  Lemma vsequiv_lspan : forall {n t s} (vs : @vec (@vec tA n) t) (us : @vec (@vec tA n) s),
    vsequiv vs us <-> ss_eq (lspan_Struct vs) (lspan_Struct us).
  Proof.
    split; intros.
    - unfold vsequiv in H. destruct H. unfold ss_eq. intros. unfold Hbelong.
      split; intros; auto.
      + rewrite lreps_eq in H0. destruct H0 as [Q H0]. unfold lrep in *.
        destruct H1 as [cs H1]. rewrite lcomb_eq in H1. rewrite <- H0 in H1.
        rewrite mvmul_assoc in H1. exists (cs v* Q). rewrite lcomb_eq. auto.
      + rewrite lreps_eq in H. destruct H as [Q H]. unfold lrep in *.
        destruct H1 as [cs H1]. rewrite lcomb_eq in H1. rewrite <- H in H1.
        rewrite mvmul_assoc in H1. exists (cs v* Q). rewrite lcomb_eq. auto.
    - unfold ss_eq in H. unfold  Hbelong in H. 
      unfold vsequiv; split; unfold lreps, vforall; intros. 
      + specialize H with (us i). destruct H. apply H0. apply lrep_in.
      + specialize H with (vs i). destruct H. apply H. apply lrep_in.
  Qed.


  Lemma vsequiv_dim : forall {n t s} (vs : @vec (@vec tA n) t) (us : @vec (@vec tA n) s),
    vsequiv vs us -> (forall k, dim (lspan_Struct vs) k <-> dim (lspan_Struct us) k).
  Proof.
    intros. apply sseq_dim. apply vsequiv_lspan. auto.
  Qed.

  Lemma lmis_basis :
    forall {n s t} (vs : @vec (@vec tA n) s) (us : @vec (@vec tA n) t),
    lmis vs us -> basis (lspan_Struct vs) us.
  Proof.
    intros. rewrite lmis_eq in H. destruct H as [H [H0 [Q H1]]].
    unfold basis; split; auto. unfold ss_eq. intros. unfold Hbelong.
    unfold lrep in *. split; intros.
    - destruct H2 as [cs H2]. rewrite <- H1 in H2. rewrite lcomb_eq in H2. rewrite mvmul_assoc in H2.
      exists (cs v* Q). rewrite lcomb_eq. auto.
    - destruct H2 as [cs H2]. rewrite lcomb_eq in H2. rewrite vmems_eq in H. destruct H as [P [H _]].
      rewrite <- H in H2. rewrite mvmul_assoc in H2. exists (cs v* P). rewrite lcomb_eq. auto.
  Qed.

  Lemma lmis_lspan:
    forall {n s t} (vs : @vec (@vec tA n) s) (us : @vec (@vec tA n) t),
    lmis vs us -> ss_eq (lspan_Struct vs) (lspan_Struct us).
  Proof.
    intros. apply vsequiv_lspan. apply lmis_vsequiv_self. auto.
  Qed.

  Lemma rank_dim : forall {n s t} (vs : @vec (@vec tA n) s),
    rank vs t <-> dim (lspan_Struct vs) t.
  Proof.
    split; intros.
    - unfold rank, dim. destruct H as [us H]. exists us. rewrite lmis_eq in H. destruct H as [H [H0 [Q H1]]].
      unfold basis in *. split; auto. unfold ss_eq. intros. unfold Hbelong. split.
      + unfold lrep in *; intros. destruct H2 as [cs H2]. rewrite lcomb_eq in *. rewrite <- H1 in H2.
        rewrite mvmul_assoc in H2. exists (cs v* Q). rewrite lcomb_eq. auto.
      + unfold lrep in *; intros. rewrite vmems_eq in H. destruct H as [P [H _]].
         destruct H2 as [cs H2]. rewrite lcomb_eq in *. rewrite <- H in H2.
        rewrite mvmul_assoc in H2. exists (cs v* P). rewrite lcomb_eq. auto.
    - unfold dim in H. destruct H as [us H]. unfold basis in H. destruct H as [H H0].
      pose proof (rank_exist vs). destruct H1 as [t' H1]. replace t' with t in H1. auto.
      unfold rank in H1. destruct H1 as [ws H1]. apply rank_unique with (vapp us ws).
      + unfold rank. exists us. rewrite lmis_eq. repeat split.
        * unfold vmems, vforall; intros. unfold vmem, vexist.
          exists (fAddRangeR i). erewrite vnth_vapp_l. Unshelve. all : fin.
        * auto.
        * apply lmis_lspan in H1. assert (ss_eq (lspan_Struct ws) (lspan_Struct us)).
          { apply ss_eq_sym in H1. eapply ss_eq_trans. apply H1. auto.  } clear H0. clear H1.
          assert (lreps us ws). { unfold lreps, vforall. intros. unfold ss_eq in H2. specialize H2 with (ws i).
            destruct H2. clear H1. unfold Hbelong in H0. apply H0. apply lreps_refl. }
          rewrite lreps_eq in H0. destruct H0 as [Q H0]. exists (vapp mat1 Q).
          apply meq_iff_mnth. intros a b. rewrite <- H0. rewrite mnth_mmul. destruct (classic (a < t)).
          ** erewrite !vnth_vapp_l. Unshelve. all : fin. rewrite vnth_vmat1. rewrite vdot_veye_l. unfold mcol. auto.
          ** erewrite !vnth_vapp_r. Unshelve. all : fin.
      + unfold rank. exists ws. rewrite lmis_eq. assert (H2:=H1). rewrite lmis_eq in H2. destruct H2 as [H2 [H3 H4]]. repeat split.
        * unfold vmems, vforall; intros. unfold vmem, vexist.
          exists (fAddRangeAddL i). erewrite vnth_vapp_r.  Unshelve. all : fin.
        * auto.
        * apply lmis_lspan in H1. assert (ss_eq (lspan_Struct ws) (lspan_Struct us)).
          { apply ss_eq_sym in H1. eapply ss_eq_trans. apply H1. auto.  } clear H0. clear H1.
          assert (lreps ws us). { unfold lreps, vforall. intros. unfold ss_eq in H5. specialize H5 with (us i).
          destruct H5. clear H0. unfold Hbelong in H1. apply H1. apply lreps_refl. }
          rewrite lreps_eq in H0. destruct H0 as [Q H0]. exists (vapp Q mat1).
          apply meq_iff_mnth. intros a b. rewrite <- H0. rewrite mnth_mmul. destruct (classic (a < t)).
          ** erewrite !vnth_vapp_l. Unshelve. all : fin. 
          ** erewrite !vnth_vapp_r. rewrite vnth_vmat1. rewrite vdot_veye_l. unfold mcol. auto. Unshelve. all : fin.
  Qed.

  Section dim_unique_theory.
  Context {ss_n : nat}.
  Context {ss_P : @vec tA ss_n -> Prop }.
  Context `(ss : @SubSpaceStruct tA Aadd Azero Aopp Amul Aone Ainv HField _ vadd vzero vopp vscal _ ss_P).
  
  Lemma dim_unique : forall (t s : nat),
    dim ss t -> dim ss s -> t = s.
  Proof.
    intros. unfold dim in *. destruct H as [vs [H H1]]. destruct H0 as [us [H0 H2]].
    assert (dim (lspan_Struct vs) t). { unfold dim. exists vs. unfold basis. split; auto. apply ss_eq_refl. }
    assert (dim (lspan_Struct us) s). { unfold dim. exists us. unfold basis. split; auto. apply ss_eq_refl. }
    assert (ss_eq (lspan_Struct us) (lspan_Struct vs)). { eapply ss_eq_trans. apply ss_eq_sym in H2. auto. auto. }
    assert (dim (lspan_Struct vs) s). { assert (forall k, dim (lspan_Struct us) k <-> dim (lspan_Struct vs) k).
      apply sseq_dim; auto. rewrite <- H6; auto. }
    rewrite <- rank_dim in H3. rewrite <- rank_dim in H6. apply rank_unique with (vs); auto.
  Qed.

  End dim_unique_theory.

  Section lzero.
  Context {n s: nat}.

  Lemma makeSubSpace : @VectorSpace tA Aadd Azero Aopp Amul Aone Ainv HField (@vec tA n) vadd vzero vopp vscal.
  Proof.
    repeat constructor; intros.
    - apply commutative.
    - apply associative.
    - apply identityRight.
    - extensionality x. rewrite vnth_vadd. rewrite vnth_vopp. rewrite vnth_vzero. fin.
    - rewrite vscal_1_l; auto.
    - rewrite vscal_assoc. auto.
    - rewrite vscal_add. auto.
    - rewrite vscal_vadd. auto.
  Qed.
  Notation SubSpaceStruct := (@SubSpaceStruct tA Aadd Azero Aopp Amul Aone Ainv HField (@vec tA n) vadd vzero vopp vscal makeSubSpace).

  Instance lzero_Struct (vs : @vec (@vec tA s) n) : SubSpaceStruct (fun cs => lcomb cs vs = vzero) .
  Proof.
    constructor.
    - rewrite lcomb_eq. extensionality x. rewrite vnth_mvmul.
      rewrite vdot_0_l. rewrite  vnth_vzero. auto.
    - intros. pose proof u.prf. pose proof v.prf; simpl in *.
      rewrite lcomb_eq in *. extensionality x. replace (vzero x) with (vzero x + vzero x)%A.
      replace (vzero x) with ((u.val v* vs) x) at 1. replace (vzero x) with ((v.val v* vs) x) at 1.
      unfold mvmul. rewrite vdot_vadd_l. auto. rewrite H0; auto. rewrite H; auto.
      rewrite vnth_vzero. fin.
    - intros. pose proof v.prf; simpl in *. replace (vzero) with (a s* (lcomb v.val vs)).
      rewrite !lcomb_eq in *. extensionality x. unfold mvmul. rewrite vdot_vscal_l.
      rewrite vnth_vscal. auto. rewrite H. extensionality x. rewrite vnth_vscal.
      rewrite vnth_vzero. fin.
  Qed.

  End lzero.

End rank.





(*
Section examples.
  Import VectorR.
  Notation vlcomb := (@vlcomb _ _ vadd vzero vscal).
  Notation vldep := (@vldep _ Azero _ vadd vzero vscal).
  Notation vlindep := (@vlindep _ Azero _ vadd vzero vscal).
  Notation vspan := (@vspan _ _ vadd vzero vscal).
  Notation vbasis := (@vbasis _ Azero _ vadd vzero vscal).

  (* Example for "linearly dependent" *)
  Section ex1.
    (* The vectors (2, 2, 5), (3, 3, 12) and (5, 5, −1) are linearly dependent
       elements of the real vector space R3, since
       7(2, 2, 5) − 3(3, 3, 12) − (5, 5, −1) = (0, 0, 0).
       Thus if v1 = (2, 2, 5), v2 = (3, 3, 12) and v3 = (5, 5, −1), then the equation
       c1v1 + c2v2 + c3v3 = 0 is satisfied with c1 = 7, c2 = −3 and c3 = −1.) *)
    Let vecs := Vector.mkvec3 (Azero:=vzero)
                  (mkvec3 2 2 5)
                  (mkvec3 3 3 12)
                  (mkvec3 5 5 (-1)%R).
    Let coefs := mkvec3 7 (-3) (-1).
    
    Example ex1_eq1 : vlcomb coefs vecs = vzero.
    Proof. apply v3eq_iff. cbv. lra. Qed.

    Example ex1_ldep : vldep vecs.
    Proof.
      unfold vldep. exists coefs. split.
      - intro. apply v3eq_iff in H. cbv in H. ra.
      - apply ex1_eq1.
    Qed.
  End ex1.

End examples.
 *)
