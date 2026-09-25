
type __ = Obj.t

type coq_Empty_set = |

val coq_Empty_set_rect : coq_Empty_set -> 'a1

val coq_Empty_set_rec : coq_Empty_set -> 'a1

val unit_rect : 'a1 -> unit -> 'a1

val unit_rec : 'a1 -> unit -> 'a1

val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

type reflect =
| ReflectT
| ReflectF

val reflect_rect : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val implb : bool -> bool -> bool

val xorb : bool -> bool -> bool

val negb : bool -> bool

val eq_true_rect : 'a1 -> bool -> 'a1

val eq_true_rec : 'a1 -> bool -> 'a1

val eq_true_rec_r : bool -> 'a1 -> 'a1

val eq_true_rect_r : bool -> 'a1 -> 'a1

val nat_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

val nat_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

val sum_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

val sum_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

type ('a, 'e) result =
| Ok of 'a
| Error of 'e

val result_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) result -> 'a3

val result_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) result -> 'a3

val prod_rect : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

val prod_rec : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val curry : (('a1 * 'a2) -> 'a3) -> 'a1 -> 'a2 -> 'a3

val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

val list_rect : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val list_rec : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val comparison_rect : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1

val comparison_rec : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1

val coq_CompOpp : comparison -> comparison

type coq_CompareSpecT =
| CompEqT
| CompLtT
| CompGtT

val coq_CompareSpecT_rect :
  (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> comparison -> coq_CompareSpecT
  -> 'a1

val coq_CompareSpecT_rec :
  (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> comparison -> coq_CompareSpecT
  -> 'a1

val coq_CompareSpec2Type : comparison -> coq_CompareSpecT

type 'a coq_CompSpecT = coq_CompareSpecT

val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT

type coq_ID = __ -> __ -> __

val id : __ -> __
