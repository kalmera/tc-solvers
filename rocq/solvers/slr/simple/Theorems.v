From Stdlib Require Import List.
From TcSolvers Require Import
  common.instances.Chain
  common.Assumptions
  solvers.slr.common.DiscoveryOrderLaws
  common.FiniteHeight
  solvers.slr.simple.proofs.Correctness
  solvers.slr.simple.proofs.LeastSolutionProof.

Set Implicit Arguments.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

  Module Internal := Correctness.Make
    V D U S M Rk RankLaws RankFinite DL UL SL ML.
  Module Sem := Internal.Sem.
  Module R := Internal.R.

  Definition solved (final : R.state) (owner : V.t) : Prop :=
    exists value, M.lookup (R.sigma final) owner = Some value.

  Definition replay (final : R.state) :=
    Sem.rhs_eval_with (fun target => M.lookup (R.sigma final) target).

  Definition owner_post_solution (tf : R.ConstraintSystem.system)
    (final : R.state) (owner : V.t) : Prop :=
    forall direct reads effects, replay final (tf owner) direct reads effects ->
      D.leq direct (R.sigma_value final owner) = true /\
      (forall target value, List.In (target,value) effects ->
        D.leq value (R.sigma_value final target) = true).

  Definition correct_final_state (tf : R.ConstraintSystem.system)
    (roots : list V.t) (final : R.state) : Prop :=
    forall owner, List.In owner roots ->
      solved final owner /\ owner_post_solution tf final owner.

  Theorem total_correct : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      correct_final_state tf roots final.
  Proof. exact Internal.total_correct. Qed.
End Make.

Module LeastSolutionMake
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

  Module Internal := LeastSolutionProof.Make
    V D U S M Rk RankLaws RankFinite DL UL UBL SL ML.
  Module Sem := Internal.Sem.
  Module R := Internal.R.

  Module Strict := Internal.Strict.
  Definition source_strict_on :=
    Strict.source_strict_on Sem.observes_at Sem.observed_direct Sem.observed_sides.

  Theorem total_least_solution : forall tf roots (finite : Sem.finite_system tf roots),
    source_strict_on tf (Sem.support finite) roots ->
    Sem.system_monotone_on tf (Sem.support finite) ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof.
    intros tf roots finite Hstrict Hmono.
    destruct (@Internal.Total.sufficient_fuel tf roots finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |].
    exact (@Internal.solve_fuel_least_solution fuel tf roots finite final Hstrict Hmono Hrun).
  Qed.
End LeastSolutionMake.

(** Concrete audits discharge the module laws; the theorems above remain generic. *)
Module Instances.
  Module E := Chain.
  Module Rk := ListDiscoveryOrder E.V.
  Module RankLaws := ListDiscoveryOrderLaws E.V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws E.V.
  Module Correct := Make E.V E.D E.U E.S E.M Rk
    RankLaws RankFinite E.DL E.UL E.SL E.ML.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
  Module Least := LeastSolutionMake E.V E.D U E.S E.M Rk
    RankLaws RankFinite E.DL UL UBL E.SL E.ML.
End Instances.

Goal True. idtac "SLR-TC_S total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_S leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.total_least_solution.
