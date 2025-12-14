
val app : 'a1 list -> 'a1 list -> 'a1 list

val sub : int -> int -> int

module Nat :
 sig
 end

type 'tA dec =
  'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool

val nat_eq_Dec : int dec

val nat_lt_Dec : int dec

type fin = int
  (* singleton inductive, whose constructor was Fin *)

val fin2nat : int -> fin -> int

val nat2finS : int -> int -> fin

type 'tA vec = fin -> 'tA

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

val rEF2RREF :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
  dec -> int -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1 vec
  vec) * int

val toRREF :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> ('a1 rowOp list * 'a1
  vec vec) * int
