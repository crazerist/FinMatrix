
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val sub : int -> int -> int

module Nat :
 sig
 end

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val seq : int -> int -> int list

type 'tA dec =
  'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool

val nat_eq_Dec : int dec

val nat_lt_Dec : int dec

type fin = int
  (* singleton inductive, whose constructor was Fin *)

val fin2nat : int -> fin -> int

val fin0 : int -> fin

val nat2finS : int -> int -> fin

type 'tA vec = fin -> 'tA

val vrepeat : int -> 'a1 -> 'a1 vec

val vzero : 'a1 -> int -> 'a1 vec

val vset : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec

val vswap : int -> 'a1 vec -> fin -> fin -> 'a1 vec

val mcol : int -> int -> 'a1 vec vec -> fin -> 'a1 vec

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

val getcolPivot :
  'a1 -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin option

val getrowPivot :
  'a1 -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin option

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
