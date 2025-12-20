Require Import LinearEquations.
Require Import MatrixInvGE.
Require Import MatrixInvAM.
Require Import RExt.


Definition solveEqAM_R := (@solveEqAM R Rplus R0 Ropp Rmult R1 Rinv).
Definition solveEqGE_R := (@solveEqGE R Rplus R0 Ropp Rmult R1 Rinv _).
Definition SolveMatrix_R := (@SolveMatrix R Rplus R0 Ropp Rmult R1 Rinv _).
Definition toRREF'_R := (@toRREF' R Rplus R0 Ropp Rmult Rinv _).
Definition rowOpsInV_R := (@rowOpsInV R Rplus Rmult).

Extraction "ocaml_test/matrix.ml" solveEqAM_R solveEqGE_R SolveMatrix_R
toRREF'_R rowOpsInV_R.

Check nat.

