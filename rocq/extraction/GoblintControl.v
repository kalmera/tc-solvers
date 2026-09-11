From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.common.Monadic.

Set Implicit Arguments.

(** Identity-monad control used by the imperative Goblint callback adapter.
    The state operations remain callbacks, so extraction preserves their
    evaluation order. *)
Definition M (A : Type) : Type := A.

Definition ret {A : Type} (value : A) : M A := value.

Definition bind {A B : Type} (computation : M A)
    (next : A -> M B) : M B :=
  next computation.

Definition callback (V D : Type) : Type :=
  @Monadic.system V D M.

Definition eval_rhs {V D : Type}
    (get : V -> M D)
    (side : V -> D -> M unit)
    (spawn : V -> M unit)
    (body : @Monadic.transfer V D M) : M D :=
  @Monadic.eval_transfer V D M get side spawn body.

(** Eta-specialized [Monadic.solve_owner]. Keeping the callbacks as
    arguments avoids allocating an [owner_operations] record for every owner
    evaluation after extraction. [bind] must remain visible to extraction so
    effectful OCaml callbacks are not optimized away as pure [unit] values. *)
Definition solve_one {V D : Type}
    (bottom : D)
    (start_evaluation : V -> M unit)
    (get : V -> V -> M D)
    (side : V -> V -> D -> M unit)
    (spawn : V -> V -> M unit)
    (set_value : V -> D -> M unit)
    (drain_owner : V -> M unit)
    (system : callback V D)
    (owner : V) : M unit :=
  bind (start_evaluation owner) (fun _ =>
    bind
      (match system owner with
       | Some body =>
           eval_rhs (get owner) (side owner) (spawn owner) body
       | None => ret bottom
       end)
      (fun direct =>
        bind (set_value owner direct) (fun _ => drain_owner owner))).

Fixpoint solve_loop_fuel {V : Type}
    (fuel : nat)
    (pop_owner : unit -> M (option V))
    (solve_owner : V -> M unit) : M bool :=
  match fuel with
  | O => ret false
  | S remaining =>
      bind (pop_owner tt) (fun picked =>
        match picked with
        | None => ret true
        | Some owner =>
            bind (solve_owner owner) (fun _ =>
              solve_loop_fuel remaining pop_owner solve_owner)
        end)
  end.

Definition solve_all {V : Type}
    (fuel : nat)
    (initialize : list V -> M unit)
    (pop_owner : unit -> M (option V))
    (solve_owner : V -> M unit)
    (roots : list V) : M bool :=
  bind (initialize roots) (fun _ =>
    solve_loop_fuel fuel pop_owner solve_owner).

Definition drain_with_fuel {V : Type}
    (fuel : nat)
    (pop_owner : unit -> M (option V))
    (solve_owner : V -> M unit) : M Monadic.seeded_result :=
  @Monadic.drain_with_fuel V M (@ret) (@bind)
    fuel pop_owner solve_owner.

Definition solve_seeds_with_fuel {V : Type}
    (fuel : nat)
    (is_started : V -> M bool)
    (pop_owner : unit -> M (option V))
    (solve_owner : V -> M unit)
    (roots : list V) : M Monadic.seeded_result :=
  @Monadic.solve_seeds_with_fuel V M (@ret) (@bind)
    fuel is_started pop_owner solve_owner roots.

Extraction Language OCaml.
Set Extraction Output Directory "ocaml/extracted".
Extract Constant M "'a" => "'a".
Extraction Inline Monadic.eval_transfer.
Extraction "GoblintControl.ml"
  eval_rhs solve_one solve_loop_fuel solve_all
  drain_with_fuel solve_seeds_with_fuel.
