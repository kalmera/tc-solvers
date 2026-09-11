From Stdlib Require Import List.
From TcSolvers Require Export common.Interfaces.

Import ListNotations.
Set Implicit Arguments.

(** Stateful online rank assignment.  This interface is intentionally
    separate from [ORDER]: [ORDER] describes a fixed mathematical order,
    whereas observing a variable here may extend the discovery state. *)
Module Type DISCOVERY_ORDER (V : VAR).
  Parameter t : Type.
  Parameter empty : t.
  Parameter lookup : t -> V.t -> option nat.
  Parameter size : t -> nat.
  Parameter observe : t -> V.t -> t * nat.
End DISCOVERY_ORDER.

(** A fixed order may be presented to the theory as a pure numbering. *)
Module Type STATELESS_RANK (V : VAR).
  Parameter rank : V.t -> nat.
End STATELESS_RANK.

(** Reveal a stateless rank only after the corresponding variable has been
    observed.  The list records the domain of the partial relational map; it
    does not participate in rank selection. *)
Module FixedRankDiscoveryOrder
  (V : VAR) (Fixed : STATELESS_RANK V) <: DISCOVERY_ORDER V.

  Definition t := list V.t.
  Definition empty : t := [].

  Fixpoint lookup (seen : t) (x : V.t) : option nat :=
    match seen with
    | [] => None
    | y :: rest =>
        if V.eq_dec x y then Some (Fixed.rank x) else lookup rest x
    end.

  Definition size (seen : t) : nat := length seen.

  Definition observe (seen : t) (x : V.t) : t * nat :=
    match lookup seen x with
    | Some rank => (seen, rank)
    | None => (x :: seen, Fixed.rank x)
    end.
End FixedRankDiscoveryOrder.

(** Small purely functional implementation used by extracted reference
    solvers and proofs.  The most recently discovered variable is stored at
    the head.  Its rank is the length of the older tail. *)
Module ListDiscoveryOrder (V : VAR) <: DISCOVERY_ORDER V.
  Definition t := list V.t.
  Definition empty : t := [].

  Fixpoint lookup (order : t) (x : V.t) : option nat :=
    match order with
    | [] => None
    | y :: older =>
        if V.eq_dec x y
        then Some (length older)
        else lookup older x
    end.

  Definition size (order : t) : nat := length order.

  Definition observe (order : t) (x : V.t) : t * nat :=
    match lookup order x with
    | Some rank => (order, rank)
    | None => (x :: order, length order)
    end.
End ListDiscoveryOrder.
