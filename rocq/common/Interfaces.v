From Stdlib Require Import List.

Set Implicit Arguments.

(** Computational interfaces only.  Proof contracts live under [proofs/]. *)

Module Type VAR.
  Parameter t : Type.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End VAR.

Module Type DOMAIN.
  Parameter t : Type.
  Parameter bottom : t.
  Parameter join : t -> t -> t.
  Parameter leq : t -> t -> bool.
End DOMAIN.

Module Type UPDATE (V : VAR) (D : DOMAIN).
  Parameter phase : Type.
  Parameter initial_phase : bool -> V.t -> phase.
  Parameter update : bool -> V.t -> phase -> D.t -> D.t -> phase * D.t.
End UPDATE.

Module Type ORDER (V : VAR).
  Parameter lt : V.t -> V.t -> bool.
End ORDER.

Module Type SET (V : VAR).
  Parameter t : Type.
  Parameter empty : t.
  Parameter mem : V.t -> t -> bool.
  Parameter add : V.t -> t -> t.
  Parameter elements : t -> list V.t.
End SET.

Module Type MAP (V : VAR).
  Parameter t : Type -> Type.
  Parameter empty : forall A : Type, t A.
  Parameter lookup : forall {A : Type}, t A -> V.t -> option A.
  Parameter update : forall {A : Type}, t A -> V.t -> A -> t A.
  Parameter values : forall {A : Type}, t A -> list A.
End MAP.

Module Type QUEUE (V : VAR) (O : ORDER V).
  Parameter t : Type.
  Parameter empty : unit -> t.
  Parameter insert : V.t -> t -> t.
  Parameter insert_all : list V.t -> t -> t.
  Parameter peek_max : t -> option V.t.
  Parameter pop_max : t -> option (V.t * t).
End QUEUE.
