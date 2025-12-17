(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : test for matrix gauss elimination
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
 *)

Require Import LinearEquations.
Require Import QcExt RExt.




(* sm2REF *)
Section test.

  Import QcExt.
  Notation getcolPivot := (getcolPivot (Azero:=0)).
  Notation getrowPivot := (getrowPivot (Azero:=0)).
  Notation sm2REF := (@sm2REF _ Qcplus 0 Qcopp Qcmult Qcinv _).
  Notation smElimDown := (@smElimDown _ Qcplus 0 Qcopp Qcmult _).
  Notation toREF := (@toREF _ Qcplus 0 Qcopp Qcmult Qcinv _).
  Notation REF2RREF := (@REF2RREF _ Qcplus 0 Qcopp Qcmult _).
  Notation toRREF := (@toRREF _ Qcplus 0 Qcopp Qcmult Qcinv _).
  Notation toRREF' := (@toRREF' _ Qcplus 0 Qcopp Qcmult Qcinv _).
  Notation ElimDown := (@ElimDown _ Qcplus 0 Qcopp Qcmult _).
  Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1 _).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Infix "*" := mmul : mat_scope.
  Check @SolveMatrix.
  Notation SolveMatrix := (@SolveMatrix _ Qcplus 0 Qcopp Qcmult 1 Qcinv _).



  (* 行阶梯形 *)
  (*      [  0 -2  1]     [0    1/3  0]   [1 0 -2/3] *)
  (*      [  3  0 -2]  => [-1/2   0  0] * [0 1 -1/2] *)
  (*      [ -2  3  0]     [9      4  6]   [0 0    1] *)

  (* 
  Let M : smat Qc 3 := l2m 0 (dlistQ2Qc [[0;-2;1];[3;0;-2];[-2;3;0]]%Q).
  Let M1 : smat Qc 3 := l2m 0 (dlistQ2Qc [[1;0;-2/3];[0;1;-1/2];[0;0;1]]%Q).
  Let E1 : smat Qc 3 := l2m 0 (dlistQ2Qc [[0;1/3;0];[-1/2;0;0];[9;4;6]]%Q).
  
  Goal match sm2REF M 3 with
       | Some (l1',M1') => m2l (rowOps2mat l1') = m2l E1
                          /\ m2l M1' = m2l M1
       | _ => False
       end.
  Proof.
    cbv; split; list_eq; f_equal; apply proof_irrelevance.
  Qed.
  


  Goal match toREF M 3 3 with (l1',M1') =>
    m2l (rowOps2mat l1') = m2l E1 /\ m2l M1' = m2l M1 end.
  Proof.
    cbv; split; list_eq; f_equal; apply proof_irrelevance.
  Qed.

  (* E1 will transform M to M1 *)
  Goal (E1 * M)%M = M1.
  Proof. apply m2l_inj. cbv. list_eq; f_equal. Qed.

  *)
  Let M : mat Qc 1 1 := l2m 0 ( [[1]]).
  Let b : @vec Qc 1 := l2v 0 ([1]).
  Let ans := SolveMatrix M b.

  Compute (v2l (snd ans)).
  Compute (lv2dl (fst ans)).

  Let M' : mat Qc 3 4 := l2m 0 (dlistQ2Qc [[2;0;5;6];[0;0;1;1];[0;0;2;2]]%Q).
  Let b' : @vec Qc 3 := l2v 0 (listQ2Qc [9;-4;-8]).

  Let ans' := SolveMatrix M' b'.

  Compute (v2l (snd ans')).
  Compute (lv2dl (fst ans')).

  Notation rowOpsInV := (@rowOpsInV _ Qcplus Qcmult ).
  Notation hasAnswers := (@hasAnswers _ 0 _).
  Notation vzero := (@vzero _ 0 _).
  Check @isRREFSolve.
  Notation isRREFSolve := (@isRREFSolve _ 0 Qcinv  _).
  Notation isRREFSolve_helper := (@isRREFSolve_helper _ 0 Qcopp).

  Compute
    let '(l, N, num, V) := toRREF' M' in
    let B := rowOpsInV l b' in
    v2l(isRREFSolve_helper V N&[#3] 2 3).
    lv2dl (fst (isRREFSolve N B V num 4 (nil, vzero))).
  Compute hasAnswers b' 2.

  Compute (v2l (snd ans')).

  Compute ans.

  Goal match toRREF M with (l1',M1', num) =>
    m2l (rowOps2mat l1') = m2l E1 /\ m2l M1' = m2l M1 end.
  Proof.
    cbv; split; list_eq; f_equal; apply UIP.
  Qed.

  (* E1 will transform M to M1 *)
  Goal (E1 * M)%M = M1.
  Proof. apply m2l_inj. cbv. list_eq; f_equal; apply UIP. Qed.

End test.


(* smElimUp *)
Section test.

  Import QcExt.
  Notation smElimUp := (@smElimUp _ Qcplus 0 Qcopp Qcmult _).

  Let M : smat Qc 3 := l2m 0 (dlistQ2Qc [[1;2;3];[4;5;6];[7;8;1]]%Q).
  (* Compute m2l (snd (smElimUp M 2 #2)). *)
End test.


Section test.
  Import QcExt.
  Open Scope mat_scope.

  Notation smat n := (smat Qc n).
  Notation mat1 := (@mat1 _ 0 1).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
  Infix "*" := mmul : mat_scope.
  Notation sm2REF := (@sm2REF _ Qcplus 0 Qcopp Qcmult Qcinv).
  Notation sm2RREF := (@sm2RREF _ Qcplus 0 Qcopp Qcmult).
  Notation smElimUp := (@smElimUp _ Qcplus 0 Qcopp Qcmult).
  Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1).
  Notation rowOps2matInv := (@rowOps2matInv _ Qcplus 0 Qcopp Qcmult 1 Qcinv).
  
  (*
                                  [ 0 -2  1]
                                  [ 3  0 -2]                 M0
                                  [-2  3  0]

  sm2REF
                  [0    1/3  0]   [ 0 -2  1]   [1 0 -2/3]
                  [-1/2   0  0] * [ 3  0 -2] = [0 1 -1/2]    T1 * M0 = M1
                  [9      4  6]   [-2  3  0]   [0 0    1]

  sm2RREF
    [1  0  2/3]   [0    1/3  0]   [ 0 -2  1]   [1 0 0]
    [0  1  1/2] * [-1/2   0  0] * [ 3  0 -2] = [0 1 0]       T2 * T1 * M0 = M2
    [0  0    1]   [9      4  6]   [-2  3  0]   [0 0 1]

  inversion
                        [6 3 4]   [ 0 -2  1]   [1 0 0]
                        [4 2 3] * [ 3  0 -2] = [0 1 0]       N0 * M0 = I
                        [9 4 6]   [-2  3  0]   [0 0 1]
   *)

  (* initial matrix M0 *)
  Let M0 : smat 3 := l2m 0 (dlistQ2Qc [[0;-2;1];[3;0;-2];[-2;3;0]]%Q).
  (* N0 is inverse matrix of M0 *)
  Let N0 : smat 3 := l2m 0 (dlistQ2Qc [[6;3;4];[4;2;3];[9;4;6]]%Q).

  (* verify that M0 and N0 are mutually inverse *)
  Goal M0 * N0 = mat1. Proof. meq. Qed.
  Goal N0 * M0 = mat1. Proof. meq. Qed.
  
  (* the REF of M0 is M1 *)
  Let l1 := match sm2REF M0 3 with Some (l1,M1) => l1 | _ => [] end.
  Let T1 : smat 3 := rowOps2mat l1.
  Let M1 : smat 3 := match sm2REF M0 3 with Some (l1,M1) => M1 | _ => mat1 end.
  
  (* the RREF of M1 is M2 *)
  Let l2 := fst (sm2RREF M1 3).
  Let T2 : smat 3 := rowOps2mat l2.
  Let M2 : smat 3 := snd (sm2RREF M1 3).

  (* verify M2 is identity matrix *)
  Goal M2 = mat1. Proof. meq; f_equal; apply proof_irrelevance. Qed.

  (* verify that (T2*T1) is N0 (i.e., inversion of M0) *)
  Goal T2 * T1 = N0. Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
  (* We can calculate inversion directly *)
  (* Compute m2l (T2 * T1). *)

  (* 我们还能得到以下结论：
     1. 根据 T1 * M0 = M1 得到 M0 = T1\-1 * M1
     2. 根据 T2 * M1 = E  得到 M1 = T2\-1
     3. 根据 T2 * T1 * M0 = E 得到 M0 = T1\-1 * T2\-1
     注意，由于 T1 和 T2 是由初等行变换构造的，其逆矩阵 (T1\-1, T2\-1)很容易求得。*)
  Goal rowOps2matInv l1 * M1 = M0. Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
  Goal rowOps2matInv l2 = M1. Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
  Goal rowOps2matInv l1 * rowOps2matInv l2 = M0.
  Proof. meq; f_equal; apply proof_irrelevance. Qed.

  (* 并猜测 rowOps2matInv_app 性质 *)
  Goal rowOps2matInv (l2 ++ l1) = M0.
  Proof. meq; f_equal; apply proof_irrelevance. Qed.
  
End test.
