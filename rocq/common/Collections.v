From Stdlib Require Import List.
From TcSolvers Require Export common.Interfaces.

Import ListNotations.
Set Implicit Arguments.

(** Simple persistent implementations used for execution and extraction tests.
    Production adapters may replace them, for example by OCaml 5 [Pqueue]. *)

Module ListSet (V : VAR).
  Definition t := list V.t.
  Definition empty : t := [].

  Definition mem (x : V.t) (xs : t) : bool :=
    if List.in_dec V.eq_dec x xs then true else false.

  Definition add (x : V.t) (xs : t) : t :=
    if List.in_dec V.eq_dec x xs then xs else x :: xs.

  Definition elements (xs : t) : list V.t := xs.
End ListSet.

Module AssocMap (V : VAR).
  Definition t (A : Type) := list (V.t * A).
  Definition empty (A : Type) : t A := [].

  Fixpoint lookup {A : Type} (m : t A) (x : V.t) : option A :=
    match m with
    | [] => None
    | (y, value) :: rest =>
        if V.eq_dec x y then Some value else lookup rest x
    end.

  Fixpoint update {A : Type} (m : t A) (x : V.t) (value : A) : t A :=
    match m with
    | [] => [(x, value)]
    | (y, old) :: rest =>
        if V.eq_dec x y
        then (y, value) :: rest
        else (y, old) :: update rest x value
    end.

  Fixpoint values {A : Type} (m : t A) : list A :=
    match m with
    | [] => []
    | (_, value) :: rest => value :: values rest
    end.
End AssocMap.

Module OrderedListQueue (V : VAR) (O : ORDER V).
  Definition t := list V.t.
  Definition empty (_ : unit) : t := [].

  Fixpoint insert_fresh (x : V.t) (q : t) : t :=
    match q with
    | [] => [x]
    | y :: rest =>
        if O.lt y x then x :: y :: rest
        else y :: insert_fresh x rest
    end.

  Definition insert (x : V.t) (q : t) : t :=
    if List.in_dec V.eq_dec x q then q else insert_fresh x q.

  Fixpoint insert_all (xs : list V.t) (q : t) : t :=
    match xs with
    | [] => q
    | x :: rest => insert_all rest (insert x q)
    end.

  Definition peek_max (q : t) : option V.t :=
    match q with
    | [] => None
    | x :: _ => Some x
    end.

  Definition pop_max (q : t) : option (V.t * t) :=
    match q with
    | [] => None
    | x :: rest => Some (x, rest)
    end.
End OrderedListQueue.
