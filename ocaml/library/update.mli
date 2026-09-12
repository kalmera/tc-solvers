open Interfaces

(** Two direct copies, then one widening/narrowing box, with widening fallback.
    Suggested policy for ordinary clients. *)
module TwoCopy (V : VAR) (D : BOX_DOMAIN) :
  UPDATE with type variable = V.t and type value = D.t

(** Zero-copy widening/narrowing box with widening fallback. *)
module WidenNarrow (V : VAR) (D : BOX_DOMAIN) :
  UPDATE with type variable = V.t and type value = D.t

(** Join iteration for finite-height domains. *)
module Join (V : VAR) (D : DOMAIN) :
  UPDATE with type variable = V.t and type value = D.t
