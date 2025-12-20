
type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val add : int -> int -> int

val sub : int -> int -> int

val even : int -> bool

val odd : int -> bool

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val ltb : int -> int -> bool

  val even : int -> bool

  val pow : int -> int -> int
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val size_nat : positive -> int

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_nat : int -> positive

  val of_succ_nat : int -> positive
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val seq : int -> int -> int list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)
 end

type q = { qnum : z; qden : positive }

type cReal = { seq0 : (z -> q); scale : z }

type dReal = (q -> bool)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val req_dec_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

type 'tA dec =
  'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool

val nat_eq_Dec : int dec

val nat_lt_Dec : int dec

val req_Dec : RbaseSymbolsImpl.coq_R dec

type fin = int
  (* singleton inductive, whose constructor was Fin *)

val fin2nat : int -> fin -> int

val fin0 : int -> fin

val nat2finS : int -> int -> fin

val nat2fin : int -> int -> fin

val seqsumAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1

val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1

val seqprodAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1

val seqprod : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1

type 'tA vec = fin -> 'tA

val vrepeat : int -> 'a1 -> 'a1 vec

val vzero : 'a1 -> int -> 'a1 vec

val v2f : 'a1 -> int -> 'a1 vec -> int -> 'a1

val vmap : int -> ('a1 -> 'a2) -> 'a1 vec -> 'a2 vec

val vmap2 : int -> ('a1 -> 'a2 -> 'a3) -> 'a1 vec -> 'a2 vec -> 'a3 vec

val vset : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec

val vswap : int -> 'a1 vec -> fin -> fin -> 'a1 vec

val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1

val vdot :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1
  vec -> 'a1

val mcol : int -> int -> 'a1 vec vec -> fin -> 'a1 vec

val m2f : 'a1 -> int -> int -> 'a1 vec vec -> int -> int -> 'a1

val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec

val mscal :
  ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 vec vec -> 'a1 vec vec

val mmulv :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec
  vec -> 'a1 vec -> 'a1 vec

val mrowScale :
  ('a1 -> 'a1 -> 'a1) -> int -> int -> fin -> 'a1 -> 'a1 vec vec -> 'a1 vec
  vec

val mrowAdd :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> fin -> fin ->
  'a1 -> 'a1 vec vec -> 'a1 vec vec

val mrowSwap : int -> int -> fin -> fin -> 'a1 vec vec -> 'a1 vec vec

type 'tA rowOp =
| ROnop
| ROswap of fin * fin
| ROscale of fin * 'tA
| ROadd of fin * fin * 'tA

val rowOps2mat :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1
  rowOp list -> 'a1 vec vec

val getcolPivot :
  'a1 -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin option

val getrowPivot :
  'a1 -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin option

val smElimDown :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
  dec -> int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec

val sm2REF :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1
  vec vec) option

val smElimUp :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
  dec -> int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec

val sm2RREF :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
  dec -> int -> 'a1 vec vec -> int -> 'a1 rowOp list * 'a1 vec vec

val setPivotAone :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> int -> int -> 'a1 vec vec -> int ->
  int -> fin -> 'a1 rowOp list * 'a1 vec vec

val elimDown :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
  dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin -> 'a1 rowOp
  list * 'a1 vec vec

val elimUp :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
  dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin -> 'a1 rowOp
  list * 'a1 vec vec

val toREF :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> int -> 'a1 rowOp
  list * 'a1 vec vec

val rEF2RREF' :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
  dec -> int -> int -> 'a1 vec vec -> int -> (('a1 rowOp list * 'a1 vec
  vec) * int) * fin vec

val toRREF' :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> (('a1 rowOp list * 'a1
  vec vec) * int) * fin vec

type 'tA answers = 'tA vec list * 'tA vec

val rowOpsInV :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 rowOp list -> 'a1
  vec -> 'a1 vec

val isRREFSolve_helper :
  'a1 -> ('a1 -> 'a1) -> 'a1 -> int -> int -> fin vec -> 'a1 vec -> int ->
  int -> 'a1 vec

val isRREFSolve :
  'a1 -> ('a1 -> 'a1) -> 'a1 -> int -> int -> 'a1 vec vec -> 'a1 vec -> fin
  vec -> int -> int -> 'a1 answers -> 'a1 answers

val hasAnswers_aux : 'a1 -> 'a1 dec -> int -> 'a1 vec -> int -> bool

val hasAnswers : 'a1 -> 'a1 dec -> int -> 'a1 vec -> int -> bool

val solveMatrix :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> 'a1 vec -> 'a1
  answers

module Coq_method3 :
 sig
  val perm1 : 'a1 -> 'a1 list -> 'a1 list list

  val perm : 'a1 list -> 'a1 list list
 end

val ronum1 : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> int

val ronum : ('a1 -> 'a1 -> bool) -> 'a1 list -> int

val mdet :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  int -> 'a1 vec vec -> 'a1

val msubmat : int -> 'a1 vec vec -> fin -> fin -> 'a1 vec vec

val mminor :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  int -> 'a1 vec vec -> fin -> fin -> 'a1

val mcofactor :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  int -> 'a1 vec vec -> fin -> fin -> 'a1

val madj :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  int -> 'a1 vec vec -> 'a1 vec vec

val minvGE :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec

val solveEqGE :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec

val minvAM :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec vec

val solveEqAM :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec

val solveEqAM_R :
  int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec ->
  RbaseSymbolsImpl.coq_R vec

val solveEqGE_R :
  int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec ->
  RbaseSymbolsImpl.coq_R vec

val solveMatrix_R_aux :
  int -> int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec
  -> RbaseSymbolsImpl.coq_R answers

val solveMatrix_R :
  int -> int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec
  -> RbaseSymbolsImpl.coq_R vec
