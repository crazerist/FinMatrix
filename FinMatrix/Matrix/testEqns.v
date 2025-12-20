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
  (*[{| this := 249 # 20; canon := Qred_involutive (249 # 20)
|};
{|
this := 550722510404 # 44235747755;
canon :=
Qred_involutive
(289688197438377717950355168335192072584020
# 23268658512041165429754843333923581778775)
|};
{|
this := 547646354858 # 44235747755;
canon :=
Qred_involutive
(1152280376236169117638771380989769336953160
# 93074634048164661719019373335694327115100)
|};
{|
this := 2181738269881 # 176942991020;
canon :=
Qred_involutive
(2295253289067521769105640824645969241194810
# 186149268096329323438038746671388654230200)
|};
{|
this := 2181345569173 # 176942991020;
canon :=
Qred_involutive
(229484015628981910394632278470867143565973
# 18614926809632932343803874667138865423020)
|};
{|
this := -247 # 200;
canon :=
Qred_involutive
(-25985131682665133965471705875447
# 21040592455599298757466968320200)
|};
{|
this := -12350 # 10033;
canon :=
Qred_involutive
(-1299256584133256698273585293772350
# 1055501320535138822168330465782833)
|};
{|
this := -50196583 # 8847149551;
canon :=
Qred_involutive
(-5280829227833320074104937725216449383
# 930746340481646617190193733356943271151)
|};
{|
this := 32725059 # 2211787387750;
canon :=
Qred_involutive
(1530121398898759849326073841843724204000
# 103416260053516290798910414817438141239000000)
|};
{|
this := 459303567371787291 # 17752690289036600000000;
canon :=
Qred_involutive
(148975140241327731772096751626341
# 5758086183836018775784534566600000000)
|}]*)
  Compute (lv2dl (fst ans)).
  (*[]*)
  Compute (v2l (mmulv M (snd ans))).
  (*[{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 249 # 20; canon := Qred_involutive (249 # 20)
|}; {| this := 1 # 20; canon := Qred_involutive (1 # 20)
|};
{| this := -247 # 200; canon := Qred_involutive
(-247 # 200) |}]*)
 

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
  (*[{|
this := -12900100 # 110607;
canon :=
Qred_involutive (-735478419438900 # 6306079917123)
|};
{|
this := 6446000 # 36869;
canon := Qred_involutive (95279931054000 # 544969869381)
|};
{|
this := -32238100 # 110607;
canon := Qred_involutive
(-158839794462300 # 544969869381)
|}; {| this := 0; canon := Qred_involutive 0 |};
{|
this := 124346000 # 1364153;
canon := Qred_involutive (180177354000 # 1976657697)
|};
{|
this := 6893000 # 15801;
canon := Qred_involutive (696193000 # 1595901)
|};
{|
this := -11275000 # 17871;
canon := Qred_involutive (-50106100000 # 79418724)
|}; {| this := 0; canon := Qred_involutive 0 |}]*)
  Compute (lv2dl (fst ans)).
  (*[[{| this := 1; canon := Qred_involutive 1 |};
{| this := 1; canon := Qred_involutive 1 |};
{| this := 1; canon := Qred_involutive 1 |};
{| this := 1; canon := Qred_involutive 1 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |}];
[{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 1; canon := Qred_involutive 1 |};
{| this := -1; canon := Qred_involutive (-1) |};
{| this := -1; canon := Qred_involutive (-1) |};
{| this := 1; canon := Qred_involutive 1 |}]]*)

  Compute (v2l (mmulv M (snd ans))).
  (*[{|
this := 500;
canon := Qred_involutive (12483580050000 # 24967160100)
|};
{|
this := 300;
canon := Qred_involutive (7490148030000 # 24967160100)
|}; {| this := -100; canon := Qred_involutive (-100) |};
{|
this := 50;
canon := Qred_involutive (67966158050 # 1359323161)
|};
{|
this := -120;
canon := Qred_involutive (-1468069013880 # 12233908449)
|}; {| this := 0; canon := Qred_involutive
(0 # 12233908449) |}]*)

  Compute (v2l (mmulv M (nth 0 (fst ans) vzero))).
  (*[{| this := 0; canon := Qred_involutive 0.000000 |};
{| this := 0; canon := Qred_involutive 0.000000 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive (0 # 400) |};
{| this := 0; canon := Qred_involutive (0 # 400) |};
{| this := 0; canon := Qred_involutive (0 # 625) |}]*)

Compute (v2l (mmulv M (nth 1 (fst ans) vzero))).
(*[{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |};
{| this := 0; canon := Qred_involutive 0 |}]*)

End test2.