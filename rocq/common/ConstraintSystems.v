From TcSolvers Require Export common.Interfaces.

Set Implicit Arguments.

(** Constructor-level signature used by proof-only common semantics.  Solver
    implementations keep the concrete inductive module below. *)
Module Type S (V : VAR) (D : DOMAIN).
  Parameter rhs : Type.
  Parameter Ret : D.t -> rhs.
  Parameter Get : V.t -> (D.t -> rhs) -> rhs.
  Parameter Side : V.t -> D.t -> rhs -> rhs.
  Parameter Spawn : V.t -> rhs -> rhs.
  Definition system := V.t -> rhs.
End S.

(** Constraint systems shared by all solver variants. *)
Module Make (V : VAR) (D : DOMAIN).

  Inductive rhs : Type :=
  | Ret : D.t -> rhs
  | Get : V.t -> (D.t -> rhs) -> rhs
  | Side : V.t -> D.t -> rhs -> rhs
  | Spawn : V.t -> rhs -> rhs.

  Definition system := V.t -> rhs.

End Make.
