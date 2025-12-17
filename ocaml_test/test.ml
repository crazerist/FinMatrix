
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

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

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Int.succ start) len0))
    len

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

(** val fin0 : int -> fin **)

let fin0 _ =
  0

(** val nat2finS : int -> int -> fin **)

let nat2finS n i =
  let s = nat_lt_Dec i (Int.succ n) in if s then i else 0

type 'tA vec = fin -> 'tA

(** val vrepeat : int -> 'a1 -> 'a1 vec **)

let vrepeat _ a _ =
  a

(** val vzero : 'a1 -> int -> 'a1 vec **)

let vzero azero n =
  vrepeat n azero

(** val vset : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec **)

let vset n a i x j =
  if nat_eq_Dec (fin2nat n j) (fin2nat n i) then x else a j

(** val vswap : int -> 'a1 vec -> fin -> fin -> 'a1 vec **)

let vswap n a i j k =
  if nat_eq_Dec (fin2nat n k) (fin2nat n i)
  then a j
  else if nat_eq_Dec (fin2nat n k) (fin2nat n j) then a i else a k

(** val mcol : int -> int -> 'a1 vec vec -> fin -> 'a1 vec **)

let mcol _ _ m j i =
  m i j

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

(** val rEF2RREF' :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    dec -> int -> int -> 'a1 vec vec -> int -> (('a1 rowOp list * 'a1 vec
    vec) * int) * fin vec **)

let rec rEF2RREF' aadd azero aopp amul hAeqDec r c m x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ((([], m), 0), (fun _ -> fin0 c)))
    (fun x' ->
    let fx = nat2finS r x' in
    (match getrowPivot azero hAeqDec r c m (Int.succ c) fx with
     | Some a ->
       let (p, v) = rEF2RREF' aadd azero aopp amul hAeqDec r c m x' in
       let (p0, n) = p in
       let (l1, m1) = p0 in
       let (l2, m2) = elimUp aadd azero aopp amul hAeqDec r c m1 x' fx a in
       ((((app l2 l1), m2), (Int.succ n)), (fun i ->
       if nat_eq_Dec (fin2nat (Int.succ r) i) x' then a else v i))
     | None -> rEF2RREF' aadd azero aopp amul hAeqDec r c m x'))
    x

(** val toRREF' :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
    -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> (('a1 rowOp list * 'a1
    vec vec) * int) * fin vec **)

let toRREF' aadd azero aopp amul ainv hAeqDec r c m =
  let (l1, m1) =
    toREF aadd azero aopp amul ainv hAeqDec r c m (Int.succ r) (Int.succ c)
  in
  let (p, v) = rEF2RREF' aadd azero aopp amul hAeqDec r c m1 (Int.succ r) in
  let (p0, num) = p in let (l2, m2) = p0 in ((((app l2 l1), m2), num), v)

type 'tA answers = 'tA vec list * 'tA vec

(** val rowOpsInV :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 rowOp list ->
    'a1 vec -> 'a1 vec **)

let rowOpsInV aadd amul s l v =
  fold_right (fun op e ->
    match op with
    | ROnop -> e
    | ROswap (i, j) -> vswap (Int.succ s) e i j
    | ROscale (i, c) ->
      (fun j ->
        if nat_eq_Dec (fin2nat (Int.succ s) j) (fin2nat (Int.succ s) i)
        then amul c (e j)
        else e j)
    | ROadd (i, j, c) ->
      (fun x ->
        if nat_eq_Dec (fin2nat (Int.succ s) x) (fin2nat (Int.succ s) i)
        then aadd (e x) (amul c (e j))
        else e x)) v l

(** val isRREFSolve_helper :
    'a1 -> ('a1 -> 'a1) -> 'a1 -> int -> int -> fin vec -> 'a1 vec -> int ->
    int -> 'a1 vec **)

let isRREFSolve_helper azero aopp aone r c v v0 x y =
  vset (Int.succ c)
    (fold_left (fun v' i ->
      vset (Int.succ c) v' (v (nat2finS r i)) (aopp (v0 (nat2finS r i))))
      (seq 0 x) (vzero azero (Int.succ c))) (nat2finS c y) aone

(** val isRREFSolve :
    'a1 -> ('a1 -> 'a1) -> 'a1 -> int -> int -> 'a1 vec vec -> 'a1 vec -> fin
    vec -> int -> int -> 'a1 answers -> 'a1 answers **)

let rec isRREFSolve azero aopp aone r c m b v x y ans =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ans)
    (fun x' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> ans)
      (fun y' ->
      let a = v (nat2finS r x') in
      if nat_eq_Dec (fin2nat (Int.succ c) a) y'
      then isRREFSolve azero aopp aone r c m b v x' y' ((fst ans), (fun i ->
             if nat_eq_Dec (fin2nat (Int.succ c) i) x'
             then b (nat2finS r x')
             else snd ans i))
      else isRREFSolve azero aopp aone r c m b v x y'
             (((isRREFSolve_helper azero aopp aone r c v
                 (mcol (Int.succ r) (Int.succ c) m (nat2finS c y')) x y') :: 
             (fst ans)), (snd ans)))
      y)
    x

(** val hasAnswers_aux : 'a1 -> 'a1 dec -> int -> 'a1 vec -> int -> bool **)

let rec hasAnswers_aux azero aeqDec r b x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun x' ->
    if aeqdec aeqDec (b (nat2finS r (sub r x'))) azero
    then hasAnswers_aux azero aeqDec r b x'
    else false)
    x

(** val hasAnswers : 'a1 -> 'a1 dec -> int -> 'a1 vec -> int -> bool **)

let hasAnswers azero aeqDec r b x =
  hasAnswers_aux azero aeqDec r b (sub (Int.succ r) x)

(** val solveMatrix :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> ('a1 -> 'a1) -> 'a1 dec -> int -> int -> 'a1 vec vec -> 'a1 vec -> 'a1
    answers **)

let solveMatrix aadd azero aopp amul aone ainv aeqDec r c m b =
  let (p, v) = toRREF' aadd azero aopp amul ainv aeqDec r c m in
  let (p0, num) = p in
  let (l, n) = p0 in
  let b' = rowOpsInV aadd amul r l b in
  if hasAnswers azero aeqDec r b' num
  then isRREFSolve azero aopp aone r c n b' v num (Int.succ c) ([],
         (vzero azero (Int.succ c)))
  else ([], (vzero azero (Int.succ c)))
