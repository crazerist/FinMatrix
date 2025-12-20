
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

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

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val even : int -> bool **)

let rec even n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun n' -> even n')
      n0)
    n

(** val odd : int -> bool **)

let odd n =
  negb (even n)

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Int.succ n) m

  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Int.succ (size_nat p0)
  | XO p0 -> Int.succ (size_nat p0)
  | XH -> Int.succ 0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 ->
           let (g, p) = ggcdn n0 a b0 in
           let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ ->
           let (g, p) = ggcdn n0 a0 b in
           let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Int.succ 0)

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t -> nth m t default)
    n

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

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

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
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

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst = __

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr = __

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = (+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = fun a -> (0.0 -. a)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun a -> (1.0 /. a)

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val req_dec_T :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let req_dec_T = fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c = 0 then true
  else false

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

(** val req_Dec : RbaseSymbolsImpl.coq_R dec **)

let req_Dec =
  req_dec_T

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

(** val nat2fin : int -> int -> fin **)

let nat2fin _ i =
  i

(** val seqsumAux :
    ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1 **)

let rec seqsumAux aadd n f acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun n' -> seqsumAux aadd n' f (aadd (f n') acc))
    n

(** val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1 **)

let seqsum aadd azero n f =
  seqsumAux aadd n f azero

(** val seqprodAux :
    ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1 **)

let rec seqprodAux amul n f acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun n' -> seqprodAux amul n' f (amul (f n') acc))
    n

(** val seqprod : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1 **)

let seqprod amul aone n f =
  seqprodAux amul n f aone

type 'tA vec = fin -> 'tA

(** val vrepeat : int -> 'a1 -> 'a1 vec **)

let vrepeat _ a _ =
  a

(** val vzero : 'a1 -> int -> 'a1 vec **)

let vzero azero n =
  vrepeat n azero

(** val v2f : 'a1 -> int -> 'a1 vec -> int -> 'a1 **)

let v2f azero n a i =
  if nat_lt_Dec i n then a (nat2fin n i) else azero

(** val vmap : int -> ('a1 -> 'a2) -> 'a1 vec -> 'a2 vec **)

let vmap _ f a i =
  f (a i)

(** val vmap2 :
    int -> ('a1 -> 'a2 -> 'a3) -> 'a1 vec -> 'a2 vec -> 'a3 vec **)

let vmap2 _ f a b i =
  f (a i) (b i)

(** val vset : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec **)

let vset n a i x j =
  if nat_eq_Dec (fin2nat n j) (fin2nat n i) then x else a j

(** val vswap : int -> 'a1 vec -> fin -> fin -> 'a1 vec **)

let vswap n a i j k =
  if nat_eq_Dec (fin2nat n k) (fin2nat n i)
  then a j
  else if nat_eq_Dec (fin2nat n k) (fin2nat n j) then a i else a k

(** val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1 **)

let vsum aadd azero n a =
  seqsum aadd azero n (v2f azero n a)

(** val vdot :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec ->
    'a1 vec -> 'a1 **)

let vdot aadd azero amul n a b =
  vsum aadd azero n (vmap2 n amul a b)

(** val mcol : int -> int -> 'a1 vec vec -> fin -> 'a1 vec **)

let mcol _ _ m j i =
  m i j

(** val m2f : 'a1 -> int -> int -> 'a1 vec vec -> int -> int -> 'a1 **)

let m2f azero r c m i =
  v2f azero c (v2f (vzero azero c) r m i)

(** val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec **)

let mat1 azero aone n i j =
  if nat_eq_Dec (fin2nat n i) (fin2nat n j) then aone else azero

(** val mscal :
    ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 vec vec -> 'a1 vec vec **)

let mscal amul r c a m =
  vmap r (vmap c (amul a)) m

(** val mmulv :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1
    vec vec -> 'a1 vec -> 'a1 vec **)

let mmulv aadd azero amul _ c m a i =
  vdot aadd azero amul c (m i) a

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

(** val rowOps2mat :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1
    rowOp list -> 'a1 vec vec **)

let rowOps2mat aadd azero amul aone n l =
  fold_right (fun op m ->
    match op with
    | ROnop -> m
    | ROswap (i, j) -> mrowSwap (Int.succ n) (Int.succ n) i j m
    | ROscale (i, c) -> mrowScale amul (Int.succ n) (Int.succ n) i c m
    | ROadd (i, j, c) -> mrowAdd aadd amul (Int.succ n) (Int.succ n) i j c m)
    (mat1 azero aone (Int.succ n)) l

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

(** val smElimDown :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    dec -> int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec **)

let rec smElimDown aadd azero aopp amul hAeqDec n m x j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS n (sub (Int.succ n) x) in
    let a = m fx j in
    if aeqdec hAeqDec a azero
    then smElimDown aadd azero aopp amul hAeqDec n m x' j
    else let op1 = ROadd (fx, j, (aopp a)) in
         let m1 = mrowAdd aadd amul (Int.succ n) (Int.succ n) fx j (aopp a) m
         in
         let (l2, m2) = smElimDown aadd azero aopp amul hAeqDec n m1 x' j in
         ((app l2 (op1 :: [])), m2))
    x

(** val sm2REF :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
    -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1
    vec vec) option **)

let rec sm2REF aadd azero aopp amul ainv hAeqDec n m x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some ([], m))
    (fun x' ->
    let j = nat2finS n (sub (Int.succ n) x) in
    (match getcolPivot azero hAeqDec n n m x j with
     | Some i ->
       if nat_eq_Dec (fin2nat (Int.succ n) i) (fin2nat (Int.succ n) j)
       then let op1 = ROnop in
            let (op2, m2) =
              let c = m j j in
              ((ROscale (j, (ainv c))),
              (mrowScale amul (Int.succ n) (Int.succ n) j (ainv c) m))
            in
            let (l3, m3) = smElimDown aadd azero aopp amul hAeqDec n m2 x' j
            in
            (match sm2REF aadd azero aopp amul ainv hAeqDec n m3 x' with
             | Some p ->
               let (l4, m4) = p in
               Some ((app l4 (app l3 (op2 :: (op1 :: [])))), m4)
             | None -> None)
       else let op1 = ROswap (j, i) in
            let m1 = mrowSwap (Int.succ n) (Int.succ n) j i m in
            let (op2, m2) =
              let c = m1 j j in
              ((ROscale (j, (ainv c))),
              (mrowScale amul (Int.succ n) (Int.succ n) j (ainv c) m1))
            in
            let (l3, m3) = smElimDown aadd azero aopp amul hAeqDec n m2 x' j
            in
            (match sm2REF aadd azero aopp amul ainv hAeqDec n m3 x' with
             | Some p ->
               let (l4, m4) = p in
               Some ((app l4 (app l3 (op2 :: (op1 :: [])))), m4)
             | None -> None)
     | None -> None))
    x

(** val smElimUp :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    dec -> int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec **)

let rec smElimUp aadd azero aopp amul hAeqDec n m x j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS n x' in
    let a = m fx j in
    if aeqdec hAeqDec a azero
    then smElimUp aadd azero aopp amul hAeqDec n m x' j
    else let op1 = ROadd (fx, j, (aopp a)) in
         let m1 = mrowAdd aadd amul (Int.succ n) (Int.succ n) fx j (aopp a) m
         in
         let (l2, m2) = smElimUp aadd azero aopp amul hAeqDec n m1 x' j in
         ((app l2 (op1 :: [])), m2))
    x

(** val sm2RREF :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    dec -> int -> 'a1 vec vec -> int -> 'a1 rowOp list * 'a1 vec vec **)

let rec sm2RREF aadd azero aopp amul hAeqDec n m x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS n x' in
    let (l1, m1) = smElimUp aadd azero aopp amul hAeqDec n m x' fx in
    let (l2, m2) = sm2RREF aadd azero aopp amul hAeqDec n m1 x' in
    ((app l2 l1), m2))
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

module Coq_method3 =
 struct
  (** val perm1 : 'a1 -> 'a1 list -> 'a1 list list **)

  let rec perm1 a l = match l with
  | [] -> (a :: []) :: []
  | hl :: tl -> (a :: l) :: (map (fun x -> hl :: x) (perm1 a tl))

  (** val perm : 'a1 list -> 'a1 list list **)

  let rec perm = function
  | [] -> [] :: []
  | hl :: tl -> concat (map (perm1 hl) (perm tl))
 end

(** val ronum1 : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> int **)

let ronum1 altb a l =
  fold_left (fun n b -> add n (if altb b a then Int.succ 0 else 0)) l 0

(** val ronum : ('a1 -> 'a1 -> bool) -> 'a1 list -> int **)

let rec ronum altb = function
| [] -> 0
| x :: l' -> add (ronum1 altb x l') (ronum altb l')

(** val mdet :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> int -> 'a1 vec vec -> 'a1 **)

let mdet aadd azero aopp amul aone n m =
  let colIds = Coq_method3.perm (seq 0 n) in
  let item = fun l ->
    let x = seqprod amul aone n (fun i -> m2f azero n n m i (nth i l 0)) in
    if odd (ronum Nat.ltb l) then aopp x else x
  in
  fold_left aadd (map item colIds) azero

(** val msubmat : int -> 'a1 vec vec -> fin -> fin -> 'a1 vec vec **)

let msubmat n m i j i0 j0 =
  let i1 =
    if nat_lt_Dec (fin2nat n i0) (fin2nat (Int.succ n) i)
    then nat2finS n (fin2nat n i0)
    else nat2finS n (Int.succ (fin2nat n i0))
  in
  let j1 =
    if nat_lt_Dec (fin2nat n j0) (fin2nat (Int.succ n) j)
    then nat2finS n (fin2nat n j0)
    else nat2finS n (Int.succ (fin2nat n j0))
  in
  m i1 j1

(** val mminor :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> int -> 'a1 vec vec -> fin -> fin -> 'a1 **)

let mminor aadd azero aopp amul aone n m i j =
  mdet aadd azero aopp amul aone n (msubmat n m i j)

(** val mcofactor :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> int -> 'a1 vec vec -> fin -> fin -> 'a1 **)

let mcofactor aadd azero aopp amul aone n m i j =
  let x = mminor aadd azero aopp amul aone n m i j in
  if Nat.even (add (fin2nat (Int.succ n) i) (fin2nat (Int.succ n) j))
  then x
  else aopp x

(** val madj :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> int -> 'a1 vec vec -> 'a1 vec vec **)

let madj aadd azero aopp amul aone n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n' i j -> mcofactor aadd azero aopp amul aone n' m j i)
    n

(** val minvGE :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec **)

let minvGE aadd azero aopp amul aone ainv aeqDec n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat1 azero aone 0)
    (fun n' ->
    match sm2REF aadd azero aopp amul ainv aeqDec n' x n with
    | Some p ->
      let (l1, m1) = p in
      let (l2, _) = sm2RREF aadd azero aopp amul aeqDec n' m1 n in
      rowOps2mat aadd azero amul aone n' (app l2 l1)
    | None -> mat1 azero aone (Int.succ n'))
    n

(** val solveEqGE :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec **)

let solveEqGE aadd azero aopp amul aone ainv aeqDec n a b =
  mmulv aadd azero amul n n
    (minvGE aadd azero aopp amul aone ainv aeqDec n a) b

(** val minvAM :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec vec **)

let minvAM aadd azero aopp amul aone ainv n m =
  mscal amul n n (ainv (mdet aadd azero aopp amul aone n m))
    (madj aadd azero aopp amul aone n m)

(** val solveEqAM :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1
    -> ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec **)

let solveEqAM aadd azero aopp amul aone ainv n a b =
  mmulv aadd azero amul n n (minvAM aadd azero aopp amul aone ainv n a) b

(** val solveEqAM_R :
    int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec ->
    RbaseSymbolsImpl.coq_R vec **)

let solveEqAM_R =
  solveEqAM RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R0
    RbaseSymbolsImpl.coq_Ropp RbaseSymbolsImpl.coq_Rmult
    RbaseSymbolsImpl.coq_R1 RinvImpl.coq_Rinv

(** val solveEqGE_R :
    int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec ->
    RbaseSymbolsImpl.coq_R vec **)

let solveEqGE_R =
  solveEqGE RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R0
    RbaseSymbolsImpl.coq_Ropp RbaseSymbolsImpl.coq_Rmult
    RbaseSymbolsImpl.coq_R1 RinvImpl.coq_Rinv req_Dec

(** val solveMatrix_R_aux :
    int -> int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R
    vec -> RbaseSymbolsImpl.coq_R answers **)

let solveMatrix_R_aux =
  solveMatrix RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R0
    RbaseSymbolsImpl.coq_Ropp RbaseSymbolsImpl.coq_Rmult
    RbaseSymbolsImpl.coq_R1 RinvImpl.coq_Rinv req_Dec

(** val solveMatrix_R :
    int -> int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R
    vec -> RbaseSymbolsImpl.coq_R vec **)

let solveMatrix_R r c m b =
  snd (solveMatrix_R_aux r c m b)
