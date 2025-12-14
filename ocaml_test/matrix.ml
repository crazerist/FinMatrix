
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
 end

type 'tA dec =
  'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

(** val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool **)

let aeqdec aeqDec =
  aeqDec

(** val nat_eq_Dec : int dec **)

let nat_eq_Dec =
  (=)

(** val nat_lt_Dec : int dec **)

let nat_lt_Dec =
  (<)

type fin = int
  (* singleton inductive, whose constructor was Fin *)

(** val fin2nat : int -> fin -> int **)

let fin2nat _ f =
  f

(** val nat2finS : int -> int -> fin **)

let nat2finS n i =
  let s = nat_lt_Dec i (Int.succ n) in if s then i else 0

type 'tA vec = fin -> 'tA

(** val mrowScale :
    ('a1 -> 'a1 -> 'a1) -> int -> int -> fin -> 'a1 -> 'a1 vec vec -> 'a1 vec
    vec **)

let mrowScale amul m _ x c m0 i j =
  if nat_eq_Dec (fin2nat m i) (fin2nat m x) then amul c (m0 i j) else m0 i j

(** val mrowAdd :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> int -> fin -> fin ->
    'a1 -> 'a1 vec vec -> 'a1 vec vec **)

let mrowAdd aadd amul m _ x y c m0 i j =
  if nat_eq_Dec (fin2nat m i) (fin2nat m x)
  then aadd (m0 i j) (amul c (m0 y j))
  else m0 i j

(** val mrowSwap : int -> int -> fin -> fin -> 'a1 vec vec -> 'a1 vec vec **)

let mrowSwap m _ x y m0 i j =
  if nat_eq_Dec (fin2nat m i) (fin2nat m x)
  then m0 y j
  else if nat_eq_Dec (fin2nat m i) (fin2nat m y) then m0 x j else m0 i j

type 'tA rowOp =
| ROnop
| ROswap of fin * fin
| ROscale of fin * 'tA
| ROadd of fin * fin * 'tA

(** val getcolPivot :
    'a1 -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin option **)

let rec getcolPivot azero hAeqDec r c m x j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun x' ->
    if aeqdec hAeqDec (m (nat2finS r (sub (Int.succ r) x)) j) azero
    then getcolPivot azero hAeqDec r c m x' j
    else Some (nat2finS r (sub (Int.succ r) x)))
    x

(** val getrowPivot :
    'a1 -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin option **)

let rec getrowPivot azero hAeqDec r c m x i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun x' ->
    if aeqdec hAeqDec (m i (nat2finS c (sub (Int.succ c) x))) azero
    then getrowPivot azero hAeqDec r c m x' i
    else Some (nat2finS c (sub (Int.succ c) x)))
    x

(** val setPivotAone :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> int -> int -> 'a1 vec vec -> int
    -> int -> fin -> 'a1 rowOp list * 'a1 vec vec **)

let setPivotAone amul ainv r c m x y a =
  let i = nat2finS r (sub (Int.succ r) x) in
  if nat_eq_Dec (fin2nat (Int.succ r) a) (fin2nat (Int.succ r) i)
  then let op1 = ROnop in
       let (op2, m2) =
         let val0 = m i (nat2finS c (sub (Int.succ c) y)) in
         ((ROscale (i, (ainv val0))),
         (mrowScale amul (Int.succ r) (Int.succ c) i (ainv val0) m))
       in
       ((op2 :: (op1 :: [])), m2)
  else let op1 = ROswap (a, i) in
       let m1 = mrowSwap (Int.succ r) (Int.succ c) a i m in
       let (op2, m2) =
         let val0 = m1 i (nat2finS c (sub (Int.succ c) y)) in
         ((ROscale (i, (ainv val0))),
         (mrowScale amul (Int.succ r) (Int.succ c) i (ainv val0) m1))
       in
       ((op2 :: (op1 :: [])), m2)

(** val elimDown :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin -> 'a1 rowOp
    list * 'a1 vec vec **)

let rec elimDown aadd azero aopp amul hAeqDec r c m x i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS r (sub (Int.succ r) x) in
    let a = m fx j in
    if aeqdec hAeqDec a azero
    then elimDown aadd azero aopp amul hAeqDec r c m x' i j
    else let op1 = ROadd (fx, i, (aopp a)) in
         let m1 = mrowAdd aadd amul (Int.succ r) (Int.succ c) fx i (aopp a) m
         in
         let (l2, m2) = elimDown aadd azero aopp amul hAeqDec r c m1 x' i j in
         ((app l2 (op1 :: [])), m2))
    x

(** val elimUp :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    dec -> int -> int -> 'a1 vec vec -> int -> fin -> fin -> 'a1 rowOp
    list * 'a1 vec vec **)

let rec elimUp aadd azero aopp amul hAeqDec r c m x i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS r x' in
    let a = m fx j in
    if aeqdec hAeqDec a azero
    then elimUp aadd azero aopp amul hAeqDec r c m x' i j
    else let op1 = ROadd (fx, i, (aopp a)) in
         let m1 = mrowAdd aadd amul (Int.succ r) (Int.succ c) fx i (aopp a) m
         in
         let (l2, m2) = elimUp aadd azero aopp amul hAeqDec r c m1 x' i j in
         ((app l2 (op1 :: [])), m2))
    x

(** val toREF :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
    -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> int -> int -> 'a1
    rowOp list * 'a1 vec vec **)

let rec toREF aadd azero aopp amul ainv hAeqDec r c m x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> ([], m))
      (fun y' ->
      let i = nat2finS r (sub (Int.succ r) x) in
      let j = nat2finS c (sub (Int.succ c) y) in
      (match getcolPivot azero hAeqDec r c m x j with
       | Some a ->
         let (l1, m1) = setPivotAone amul ainv r c m x y a in
         let (l2, m2) = elimDown aadd azero aopp amul hAeqDec r c m1 x' i j in
         let (l3, m3) = toREF aadd azero aopp amul ainv hAeqDec r c m2 x' y'
         in
         ((app l3 (app l2 l1)), m3)
       | None -> toREF aadd azero aopp amul ainv hAeqDec r c m x y'))
      y)
    x

(** val rEF2RREF :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    dec -> int -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1 vec
    vec) * int **)

let rec rEF2RREF aadd azero aopp amul hAeqDec r c m x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (([], m), 0))
    (fun x' ->
    let fx = nat2finS r x' in
    (match getrowPivot azero hAeqDec r c m (Int.succ c) fx with
     | Some a ->
       let (p, n') = rEF2RREF aadd azero aopp amul hAeqDec r c m x' in
       let (l1, m1) = p in
       let (l2, m2) = elimUp aadd azero aopp amul hAeqDec r c m1 x' fx a in
       (((app l2 l1), m2), (Int.succ n'))
     | None -> rEF2RREF aadd azero aopp amul hAeqDec r c m x'))
    x

(** val toRREF :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
    -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> ('a1 rowOp list * 'a1
    vec vec) * int **)

let toRREF aadd azero aopp amul ainv hAeqDec r c m =
  let (l1, m1) =
    toREF aadd azero aopp amul ainv hAeqDec r c m (Int.succ r) (Int.succ c)
  in
  let (p, num) = rEF2RREF aadd azero aopp amul hAeqDec r c m1 (Int.succ r) in
  let (l2, m2) = p in (((app l2 l1), m2), num)
