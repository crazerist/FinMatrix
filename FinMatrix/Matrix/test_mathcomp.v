From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import rat. (* 使用有理数 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section Solver4x4.

(* 定义域为有理数 *)
Definition F := rat.

(* ========================================== *)
(* 1. 辅助函数: 从 List 构造 Matrix *)
(* ========================================== *)
Definition seq2matrix (rows : seq (seq rat)) (m n : nat) : 'M[rat]_(m, n) :=
  \matrix_(i < m, j < n) (nth 0%:Q (nth [::] rows i) j).

Definition seq2col (col : seq rat) (m : nat) : 'cV[rat]_m :=
  \col_(i < m) (nth 0%:Q col i).

(* ========================================== *)
(* 2. 数据定义 (4x4, Rank 2) *)
(* ========================================== *)

(* M = 
   [ 1  0  1  0 ]  <- 基向量 1
   [ 0  1  0  1 ]  <- 基向量 2
   [ 1  1  1  1 ]  <- Row 1 + Row 2
   [ 2  0  2  0 ]  <- 2 * Row 1
*)
Definition M_data := [::
  [:: 1%:Q];
].

Definition M : 'M[rat]_(4,4) := seq2matrix M_data 4 4.

(* 构造 b 使得方程有解。
   设目标解为 [1, 2, 0, 0]^T
   b = M * [1, 2, 0, 0]^T = [1, 2, 3, 2]^T
*)
Definition b_data := [:: 1%:Q; 2%:Q; 3%:Q; 2%:Q].
Definition b : 'cV[rat]_4 := seq2col b_data 4.

(* ========================================== *)
(* 3. 计算与验证 (使用 vm_compute 加速) *)
(* ========================================== *)

(* 计算秩 *)
Definition rank_M := \rank M.

Eval vm_compute in (rank_M : nat).

Compute rank_M.

(* 验证秩是否为 2 *)
Lemma check_rank : rank_M = 2.
Proof. by vm_compute. Qed. (* 瞬间完成 *)

(* 计算特解 xp = pinvmx(M) * b *)
Definition xp := pinvmx M *m b.

(* 验证 xp 是否真的是解 (M * xp == b) *)
Lemma check_solution : M *m xp = b.
Proof.
  apply/eqP.
  (* 4x4 矩阵，且数字较小，vm_compute 这里会非常快 *)
  Time vm_compute. 
Qed.

(* ========================================== *)
(* 4. 观察结果 (可选) *)
(* ========================================== *)

(* 如果你想看 xp 到底算出来是多少，可以用 Compute *)
(* 这里的 xp 应该是 [1/2, 1, 1/2, 1]^T (这是最小范数解，不是我们构造时的 [1,2,0,0]) *)
(* Compute xp. *)

End Solver4x4.