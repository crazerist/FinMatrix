
Require Import LinearEquations.
Require Import MatrixGauss.
Require Import QcExt RExt.


(* getcolPivot *)
Section test.
  Open Scope nat_scope.
  
  Let M : smat nat 3 := l2m 0 [[1;0;0];[0;1;0];[0;0;1]].
  Notation getcolPivot := (@getcolPivot nat 0).
  (* Compute getcolPivot M 3 #0. *)
  (* Compute getcolPivot M 3 #1. *)
  (* Compute getcolPivot M 3 #2. *)
  (* Compute getcolPivot M 2 #0. *)
  (* Compute getcolPivot M 2 #1. *)
  (* Compute getcolPivot M 2 #2. *)
  (* Compute getcolPivot M 1 #0. *)
  (* Compute getcolPivot M 1 #1. *)
  (* Compute getcolPivot M 1 #2. *)
  (* Compute getcolPivot M 0 #0. *)
  (* Compute getcolPivot M 0 #1. *)
  (* Compute getcolPivot M 0 #2. *)
End test.


(* smElimDown *)
Section test.
  Import QcExt.
  Notation smElimDown := (@smElimDown _ Qcplus 0 Qcopp Qcmult _).
  Notation ElimDown := (@ElimDown _ Qcplus 0 Qcopp Qcmult _).
  
  Let M : smat Qc 3 := l2m 0 (dlistQ2Qc [[1;2;3];[4;5;6];[7;8;9]]%Q).
  Compute m2l (snd (smElimDown M 2 #0)).
  (* Compute m2l (snd (smElimDown M 2 #0)). *)
End test.


(* sm2REF *)
Section test.

  Import QcExt.
  Notation getcolPivot := (getcolPivot (Azero:=0)).
  Notation sm2REF := (@sm2REF _ Qcplus 0 Qcopp Qcmult Qcinv _).
  Notation smElimDown := (@smElimDown _ Qcplus 0 Qcopp Qcmult _).
  Notation toREF := (@toREF _ Qcplus 0 Qcopp Qcmult Qcinv _).
  Notation ElimDown := (@ElimDown _ Qcplus 0 Qcopp Qcmult _).
  Notation rowOps2mat := (@rowOps2mat _ Qcplus 0 Qcmult 1 _).
  Notation mmul := (@mmul _ Qcplus 0 Qcmult).
    Notation solveAnswers_aux := (@solveAnswers_aux _ 0 Qcopp _).
  Infix "*" := mmul : mat_scope.

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

  Let M : mat Qc 3 4 := l2m 0 (dlistQ2Qc [[1;2;3;4];[1;3;5;7];[2;5;8;1]]%Q).
  Let M1 : mat Qc 3 4 := l2m 0 (dlistQ2Qc [[1;2;3;4];[0;1;2;3];[0;0;0;1]]%Q).
  Let E1 : smat Qc 3 := l2m 0 (dlistQ2Qc [[1;0;0];[-1;1;0];[1/10;1/10;-1/10]]%Q).

  Goal match toREF M 3 4 with (l1',M1') =>
    m2l (rowOps2mat l1') = m2l E1 /\ m2l M1' = m2l M1 end.
  Proof.
    cbv; split; list_eq; f_equal; apply proof_irrelevance.
  Qed.

  (* E1 will transform M to M1 *)
  Goal (E1 * M)%M = M1.
  Proof. apply m2l_inj. cbv. list_eq; f_equal; apply UIP. Qed.
    

    Compute (map v2l (solveAnswers_aux M1 nil 3 4))  .


End test.