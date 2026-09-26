From Stdlib Require Import List.
From TcSolvers Require Import
  common.instances.IdempotentChain
  common.instances.Chain
  common.Assumptions common.BoxUpdate common.UpdateIdempotency
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

(** Ordinary systems have no side effects. Fixedness uses first-discovery ranks
    and value-only idempotency of ordinary OneBox updates; phases may change. *)
Module OrdinaryFixedPointMake (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module Fixed := FixedPoint.Make V D WN.
  Module U := Fixed.U.
  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (UL : UPDATE_LAWS V D U) (IL : VALUE_IDEMPOTENT V D U).
    Module WithCollections (S : SET V) (M : MAP V) (Features : Restarting.FEATURES)
      (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
      Module Internal := Fixed.WithLaws S M Features DL WNL UL SL ML.
      Module Sem := Internal.Sem.
      Module R := Internal.R.

      Definition monotonic_system (tf : R.ConstraintSystem.system) : Prop := forall owner,
        Internal.N.rhs_dependencies_monotone (tf owner) /\
        Internal.N.rhs_effects_monotone (tf owner).
      (** No side contributions in any observation; spawns remain allowed. *)
      Definition no_side_effects (tf : R.ConstraintSystem.system) : Prop :=
        forall owner result, Internal.N.trace_observes (tf owner) result ->
          Internal.N.observed_sides result = nil.
      Definition solved final owner := exists value, M.lookup (R.sigma final) owner = Some value.
      Definition replay final := Sem.rhs_eval_with (fun target => M.lookup (R.sigma final) target).
      Definition correct_final_state tf roots final :=
        forall owner, List.In owner roots -> solved final owner /\
          (forall direct reads effects, replay final (tf owner) direct reads effects ->
            D.leq direct (R.sigma_value final owner) = true /\
            forall target value, List.In (target,value) effects ->
              D.leq value (R.sigma_value final target) = true).
      Definition narrowing_fixed tf final := forall owner, solved final owner ->
        (exists direct reads effects, replay final (tf owner) direct reads effects) /\
        (forall direct reads effects, replay final (tf owner) direct reads effects ->
          UL.equivalent (WN.narrow (R.sigma_value final owner) direct) (R.sigma_value final owner)).

      Theorem total_correct_and_fixed : forall tf roots,
        Sem.finite_system tf roots -> monotonic_system tf -> no_side_effects tf ->
        exists fuel final, R.solve_fuel fuel tf roots = Some final /\
          correct_final_state tf roots final /\ narrowing_fixed tf final.
      Proof.
        intros tf roots finite Hmono Hpure.
        assert (Hordinary : Internal.N.ordinary_monotonic_system tf).
        { constructor.
          - intro owner. exact (proj1 (Hmono owner)).
          - intro owner. exact (proj2 (Hmono owner)).
          - exact Hpure. }
        destruct (@Internal.total_correct_and_fixed tf roots finite
          IL.ordinary_value_idempotent Hordinary)
          as [fuel [final [Hrun [Hcorrect Hfixed]]]].
        exists fuel, final. split; [exact Hrun |]. split; [exact Hcorrect |].
        intros owner Hsolved.
        destruct (Hfixed owner Hsolved) as [direct [reads [effects [Hreplay Howner_fixed]]]].
        split; [eauto |].
        intros direct' reads' effects' Hreplay'.
        destruct (Internal.C.rhs_eval_deterministic Hreplay Hreplay') as [-> [_ _]].
        exact Howner_fixed.
      Qed.
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
  Module IE := IdempotentChain.
  Module Fixed := OrdinaryFixedPointMake IE.V IE.D IE.WN.
  Module FixedUL := IE.UpdateLaws Fixed.U.
  Module IL := IE.Idempotency Fixed.U.
  Module FixedLaws := Fixed.WithLaws IE.DL IE.WNL FixedUL IL.
  Module Ordinary := FixedLaws.WithCollections IE.S IE.M Restarting.AllEnabledFeatures
    IE.SL IE.ML.
  Definition ordinary_fixed := Ordinary.total_correct_and_fixed.
End Instances.

Goal True. idtac "SLR-TC_R total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_R leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.total_least_solution.

Goal True. idtac "SLR-TC_R ordinary narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.ordinary_fixed.
