
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Empty_set = |

(** val coq_Empty_set_rect : coq_Empty_set -> 'a1 **)

let coq_Empty_set_rect _ =
  assert false (* absurd case *)

(** val coq_Empty_set_rec : coq_Empty_set -> 'a1 **)

let coq_Empty_set_rec _ =
  assert false (* absurd case *)

(** val unit_rect : 'a1 -> unit -> 'a1 **)

let unit_rect f _ =
  f

(** val unit_rec : 'a1 -> unit -> 'a1 **)

let unit_rec f _ =
  f

(** val bool_rect : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rect f f0 = function
| true -> f
| false -> f0

(** val bool_rec : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rec f f0 = function
| true -> f
| false -> f0

type reflect =
| ReflectT
| ReflectF

(** val reflect_rect :
    (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)

let reflect_rect f f0 _ = function
| ReflectT -> f __
| ReflectF -> f0 __

(** val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)

let reflect_rec f f0 _ = function
| ReflectT -> f __
| ReflectF -> f0 __

(** val implb : bool -> bool -> bool **)

let implb b1 b2 =
  if b1 then b2 else true

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val eq_true_rect : 'a1 -> bool -> 'a1 **)

let eq_true_rect f _ =
  f

(** val eq_true_rec : 'a1 -> bool -> 'a1 **)

let eq_true_rec f _ =
  f

(** val eq_true_rec_r : bool -> 'a1 -> 'a1 **)

let eq_true_rec_r _ h =
  h

(** val eq_true_rect_r : bool -> 'a1 -> 'a1 **)

let eq_true_rect_r _ h =
  h

(** val nat_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

let rec nat_rect f f0 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> f)
    (fun n0 -> f0 n0 (nat_rect f f0 n0))
    n

(** val nat_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

let rec nat_rec f f0 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> f)
    (fun n0 -> f0 n0 (nat_rec f f0 n0))
    n

(** val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

let option_rect f f0 = function
| Some a -> f a
| None -> f0

(** val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

let option_rec f f0 = function
| Some a -> f a
| None -> f0

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

(** val sum_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let sum_rect f f0 = function
| Coq_inl a -> f a
| Coq_inr b -> f0 b

(** val sum_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let sum_rec f f0 = function
| Coq_inl a -> f a
| Coq_inr b -> f0 b

type ('a, 'e) result =
| Ok of 'a
| Error of 'e

(** val result_rect :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) result -> 'a3 **)

let result_rect f f0 = function
| Ok a -> f a
| Error e -> f0 e

(** val result_rec :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) result -> 'a3 **)

let result_rec f f0 = function
| Ok a -> f a
| Error e -> f0 e

(** val prod_rect : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

let prod_rect f = function
| (a, b) -> f a b

(** val prod_rec : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

let prod_rec f = function
| (a, b) -> f a b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val curry : (('a1 * 'a2) -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

let curry f x y =
  f (x, y)

(** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

let uncurry f = function
| (x, y) -> f x y

(** val list_rect :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rec list_rect f f0 = function
| [] -> f
| y :: l0 -> f0 y l0 (list_rect f f0 l0)

(** val list_rec :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rec list_rec f f0 = function
| [] -> f
| y :: l0 -> f0 y l0 (list_rec f f0 l0)

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val comparison_rect : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)

let comparison_rect f f0 f1 = function
| Eq -> f
| Lt -> f0
| Gt -> f1

(** val comparison_rec : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)

let comparison_rec f f0 f1 = function
| Eq -> f
| Lt -> f0
| Gt -> f1

(** val coq_CompOpp : comparison -> comparison **)

let coq_CompOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type coq_CompareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val coq_CompareSpecT_rect :
    (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> comparison ->
    coq_CompareSpecT -> 'a1 **)

let coq_CompareSpecT_rect f f0 f1 _ = function
| CompEqT -> f __
| CompLtT -> f0 __
| CompGtT -> f1 __

(** val coq_CompareSpecT_rec :
    (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> comparison ->
    coq_CompareSpecT -> 'a1 **)

let coq_CompareSpecT_rec f f0 f1 _ = function
| CompEqT -> f __
| CompLtT -> f0 __
| CompGtT -> f1 __

(** val coq_CompareSpec2Type : comparison -> coq_CompareSpecT **)

let coq_CompareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a coq_CompSpecT = coq_CompareSpecT

(** val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT **)

let coq_CompSpec2Type _ _ =
  coq_CompareSpec2Type

type coq_ID = __ -> __ -> __

(** val id : __ -> __ **)

let id x =
  x
