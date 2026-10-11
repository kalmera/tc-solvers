From Stdlib Require Export
  List Lia Arith.PeanoNat Sorting.Sorted Sorting.Permutation
  Wellfounded Wf_nat Relations.Relation_Operators
  Wellfounded.Inverse_Image Wellfounded.Lexicographic_Product.
From TcSolvers Require Export
  common.SolverInterfaces
  common.Assumptions
  common.ConstraintSemantics
  solvers.slr.common.DiscoveryOrderLaws
  common.SideUpdate
  solvers.slr.deferred_simple.DeferredSimpleInterface.

Import ListNotations.
Set Implicit Arguments.

(** Proof-only interpretation of the FIFO-Deferred Simple machine. *)
Module Semantics.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : DeferredSimple.FEATURES).

  Module Solver := DeferredSimpleInterface.Make V D U SU S M Rk Features.
  Module R := Solver.R.
  Module ConstraintSyntax := Solver.Syntax.
  Module ConstraintSemantics := Solver.TransferSemantics.
  Include ConstraintSemantics.

  Include Solver.ExecutionSemantics.
  Definition terminates_to
    (tf : R.ConstraintSystem.system)
    (initial : list V.t) (final : R.state) : Prop :=
    steps tf (R.initial_config initial) (terminal_config final) /\
    quiescent final.

  Module StateSpec := SolverSpecifications.Make V D Solver.Sem Solver.View.
  Definition solved := StateSpec.solved.
  Definition rhs_eval := StateSpec.replay.
  Definition side_effects_below := StateSpec.side_effects_below.
  Definition rhs_post_solution := StateSpec.rhs_post_solution.

  Definition correct_final_state
    (tf : R.ConstraintSystem.system)
    (initial : list V.t) (final : R.state) : Prop :=
    forall owner,
      List.In owner initial ->
      solved final owner /\
      rhs_post_solution final owner (tf owner).

  Definition totally_correct_on
    (tf : R.ConstraintSystem.system) (initial : list V.t) : Prop :=
    exists fuel final,
      R.solve_fuel fuel tf initial = Some final /\
      correct_final_state tf initial final.

Lemma supported_observed_spawns : forall supported body result,
 rhs_supported supported body -> rhs_observes body result ->
 forall target, In target (observed_spawns result) -> supported target.
Proof.
 intros supported body result Hsupported Hobs. revert Hsupported.
 induction Hobs; intros Hsupported target' Hin; inversion Hsupported; subst; cbn in Hin.
 - contradiction.
 - eapply IHHobs; eauto.
 - eapply IHHobs; eauto.
 - destruct Hin as [<-|Hin]; [assumption|eapply IHHobs; eauto].
Qed.
Lemma finite_spawn_closed : forall tf roots (finite : finite_system tf roots) values,
 spawn_closed_on tf (support finite) values.
Proof.
 intros tf roots finite values owner Hin result [Hobs Hreads] target Hspawn.
 exact (@supported_observed_spawns (fun y => In y (support finite)) (tf owner) result (system_supported finite owner Hin) Hobs target Hspawn).
Qed.


End Make.
End Semantics.
