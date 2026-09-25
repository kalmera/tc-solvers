open Datatypes
open DecidableClass

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val compare : bool -> bool -> comparison **)

let compare b1 b2 =
  if b1 then if b2 then Eq else Gt else if b2 then Lt else Eq

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

(** val coq_Decidable_eq_bool : bool -> bool -> coq_Decidable **)

let coq_Decidable_eq_bool =
  eqb

(** val ifb : bool -> bool -> bool -> bool **)

let ifb b1 b2 b3 =
  if b1 then b2 else b3

(** val orb_true_elim : bool -> bool -> bool **)

let orb_true_elim b1 _ =
  if b1 then true else false

(** val andb_false_elim : bool -> bool -> bool **)

let andb_false_elim b1 _ =
  if b1 then false else true

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val reflect_dec : bool -> reflect -> bool **)

let reflect_dec _ = function
| ReflectT -> true
| ReflectF -> false

(** val eqb_spec : bool -> bool -> reflect **)

let eqb_spec b b' =
  if b
  then if b' then ReflectT else ReflectF
  else if b' then ReflectF else ReflectT

module BoolNotations =
 struct
 end
