From Stdlib Require Import List.
From TcSolvers Require Import
  common.SolverSpecifications
  common.instances.Chain
  common.Assumptions common.BoxUpdate
  solvers.slr.common.DiscoveryOrderLaws
  common.FiniteHeight
  solvers.slr.restarting.proofs.FixedPoint
  solvers.slr.restarting.proofs.Correctness
  solvers.slr.restarting.proofs.LeastSolutionProof.

Set Implicit Arguments.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (Features : Restarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

  Module Internal := Correctness.Make
    V D U S M Rk Features RankLaws RankFinite DL UL SL ML.
  Module Sem := Internal.Sem.
  Module R := Internal.R.

  Module Spec := Internal.Spec.
  Include Spec.

  Definition terminates_to := Sem.terminates_to.

  Theorem semantic_termination : forall tf roots,
    Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
  Proof. exact Internal.solver_terminates. Qed.

  Theorem sufficient_fuel : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final.
  Proof. exact Internal.sufficient_fuel. Qed.

  Theorem successful_run_correct : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
  Proof. exact Internal.solve_fuel_spawn_correct. Qed.

  Corollary total_correct : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      correct_final_state tf roots final.
  Proof.
    intros tf roots finite.
    destruct (sufficient_fuel finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |].
    exact (@successful_run_correct fuel tf roots final Hrun).
  Qed.
End Make.

Module LeastSolutionMake
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : Restarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

  Module Internal := LeastSolutionProof.Make
    V D U S M Rk Features RankLaws RankFinite DL UL UBL SL ML.
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

(** Ordinary systems have no side effects. First-discovery ranks ensure that
    their owner frames never enter the fallback phase. Fixedness additionally
    uses repeated updates of changed controlled owners with their returned phases. *)
Module OrdinaryFixedPointMake (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module Fixed := FixedPoint.Make V D WN.
  Module U := Fixed.U.
  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (UL : UPDATE_LAWS V D U).
    Module WithCollections (S : SET V) (M : MAP V) (Features : Restarting.FEATURES)
      (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
      Module Internal := Fixed.WithLaws S M Features DL WNL UL SL ML.
      Module Sem := Internal.Sem.
      Module R := Internal.R.

      Module Spec := Internal.Spec.
      Include Spec.
      Definition narrowing_fixed := narrowing_fixed_with WN.narrow
        (fun _ _ direct => direct).

      (** Every active and suspended owner frame has a phase other than [U.Widen]. *)
      Definition control_avoids_fallback := Internal.N.control_avoids_fallback.

      (** The invariant holds throughout the run, including unfinished prefixes. *)
      Definition avoids_fallback
        (tf : R.ConstraintSystem.system) (roots : list V.t) : Prop :=
        forall c,
          Sem.steps tf (R.initial_config roots) c ->
          control_avoids_fallback (R.cfg_control c).

      (** Ordinary monotone systems never enter [U.Widen]. This holds for every
          feature setting; it does not require controlled-owner recomputation. *)
      Theorem ordinary_avoids_fallback : forall tf roots,
        Sem.finite_system tf roots -> monotonic_system tf -> no_side_effects tf ->
        avoids_fallback tf roots.
      Proof.
        intros tf roots finite Hmono Hpure.
        exact (@Internal.N.first_discovery_ordinary_avoids_fallback
          tf roots finite (Internal.ordinary_system_from_common Hmono Hpure)).
      Qed.

      Theorem successful_run_fixed : Features.recompute_controlled = true ->
        forall fuel tf roots final,
        Sem.finite_system tf roots -> monotonic_system tf -> no_side_effects tf ->
        R.solve_fuel fuel tf roots = Some final -> narrowing_fixed tf final.
      Proof. exact Internal.successful_run_narrowing_fixed. Qed.

    End WithCollections.
  End WithLaws.
End OrdinaryFixedPointMake.

(** Concrete audits discharge the module laws; the theorems above remain generic. *)
Module Instances.
  Module E := Chain.
  Module Rk := ListDiscoveryOrder E.V.
  Module RankLaws := ListDiscoveryOrderLaws E.V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws E.V.
  Module Correct := Make E.V E.D E.U E.S E.M Rk Restarting.AllEnabledFeatures
    RankLaws RankFinite E.DL E.UL E.SL E.ML.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
  Module Least := LeastSolutionMake E.V E.D U E.S E.M Rk Restarting.AllEnabledFeatures
    RankLaws RankFinite E.DL UL UBL E.SL E.ML.
  Module IE := Chain.
  Module Fixed := OrdinaryFixedPointMake IE.V IE.D IE.WN.
  Module FixedUL := IE.UpdateLaws Fixed.U.
  Module FixedLaws := Fixed.WithLaws IE.DL IE.WNL FixedUL.
  Module Ordinary := FixedLaws.WithCollections IE.S IE.M Restarting.AllEnabledFeatures
    IE.SL IE.ML.
  Module OrdinaryReaderWakeups := FixedLaws.WithCollections IE.S IE.M
    Restarting.ReaderWakeupsOnlyFeatures IE.SL IE.ML.
  Definition ordinary_fixed := Ordinary.successful_run_fixed eq_refl.
End Instances.

Goal True. idtac "SLR-TC_R total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_R leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.total_least_solution.

Goal True. idtac "SLR-TC_R ordinary no-fallback proven with assumptions:". Abort.
Print Assumptions Instances.Ordinary.ordinary_avoids_fallback.
Print Assumptions Instances.OrdinaryReaderWakeups.ordinary_avoids_fallback.

Goal True. idtac "SLR-TC_R ordinary narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.ordinary_fixed.
