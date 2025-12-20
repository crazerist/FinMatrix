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

Section test1.

  Import QcExt.
  Notation SolveMatrix := (@SolveMatrix _ Qcplus 0 Qcopp Qcmult 1 Qcinv _).
  Notation mmulv := (@mmulv _ Qcplus 0 Qcmult).
  Notation vzero := (@vzero _ 0).

  Let M : mat Qc 10 10 := l2m 0 (dlistQ2Qc [
  [ 20; -20; 0; 0; 0; 0; 0; 1; 0; 0 ];
  [ -20; (20 + 1/4700 + 1/2200); -(1/4700); 0; 0; 0; 0; 0; 0; 0 ];
  [ 0; -(1/4700); (1/4700); 0; 0; 0; 0; 0; 1; 0 ];
  [ 0; 0; 0; (1/150); -(1/150); 0; 0; 0; -1; 0 ];
  [ 0; 0; 0; -(1/150); (1/150 + 1/1000000 + 1/10000000); -(1/1000000); 0; 0; 0; 0 ];
  [ 0; 0; 0; 0; -(1/1000000); (1/1000000 + 1/330); -(1/330); 0; 0; 1 ];
  [ 0; 0; 0; 0; 0; -(1/330); (1/330 + 1/100000); 0; 0; 0 ];
  [ 1; 0; 0; 0; 0; 0; 0; 0; 0; 0 ];
  [ 0; 0; 1; -1; 0; 0; 0; 0; 0; 0 ];
  [ 0; 0; 0; 0; 0; 1; 0; 0; 0; 0 ]
  ]%Q).

  Let b : @vec Qc 10 := l2v 0 (listQ2Qc [
  0; 0; 0; 0; 0; 0; 0; 249/20;1/20;-247/200
  ]%Q).

  Let ans := SolveMatrix M b.

  Compute (v2l (snd ans)).
  Compute (lv2dl (fst ans)).

  Compute (v2l (mmulv M (snd ans))).

  Compute (v2l (mmulv M (nth 0 (fst ans) vzero))).

  End test1.

Section test2.

  Import QcExt.
  Notation SolveMatrix := (@SolveMatrix _ Qcplus 0 Qcopp Qcmult 1 Qcinv _).
  Notation mmulv := (@mmulv _ Qcplus 0 Qcmult).
  Notation vzero := (@vzero _ 0).

    Let M : mat Qc 6 8 := 
    l2m 0 (dlistQ2Qc [
      [ 707/1000;  707/1000; -707/1000; -707/1000; -259/1000;  259/1000; -259/1000;  259/1000]; (* Fx *)
      [-707/1000;  707/1000;  707/1000; -707/1000;  259/1000;  259/1000; -259/1000; -259/1000]; (* Fy *)
      [ 0;         0;         0;         0;         966/1000;  966/1000;  966/1000;  966/1000]; (* Fz *)
      [ 45/100;   -45/100;    45/100;   -45/100;   -32/100;    32/100;   -32/100;    32/100 ]; (* Mx *)
      [ 55/100;    55/100;   -55/100;   -55/100;    32/100;   -32/100;    32/100;   -32/100 ]; (* My *)
      [ 88/100;   -88/100;   -88/100;    88/100;    0;         0;         0;         0      ]  (* Mz *)
    ]%Q).

  Let b : @vec Qc 6 := 
    l2v 0 (listQ2Qc[500; 300; -100; 50; -120; 0]%Q).


  Let ans := SolveMatrix M b.

  Compute (v2l (snd ans)).
  Compute (lv2dl (fst ans)).

  Compute (v2l (mmulv M (snd ans))).

  Compute (v2l (mmulv M (nth 0 (fst ans) vzero))).

End test2.