From Stdlib Require Import List.
From TcSolvers Require Import
  common.Assumptions
  solvers.slr.common.DiscoveryOrderLaws
  common.FiniteHeight
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

  Definition replay (final : R.state) :=
    Sem.rhs_eval_with (fun target => M.lookup (R.sigma final) target).

  Definition correct_final_state (tf : R.ConstraintSystem.system)
    (roots : list V.t) (final : R.state) : Prop :=
    forall owner, List.In owner roots ->
      (exists value, M.lookup (R.sigma final) owner = Some value) /\
      (forall direct reads effects, replay final (tf owner) direct reads effects ->
        D.leq direct (R.sigma_value final owner) = true /\
        (forall target value, List.In (target,value) effects ->
          D.leq value (R.sigma_value final target) = true)).

  Theorem total_correct : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      correct_final_state tf roots final.
  Proof. exact Internal.total_correct. Qed.
End Make.

Module FirstDiscovery
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V)
  (Features : Restarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Rk := ListDiscoveryOrder V.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    ListDiscoveryOrderLaws V.
  Module Finite <: FINITE_DISCOVERY_ORDER_LAWS V Rk Laws :=
    ListFiniteDiscoveryOrderLaws V.
  Include Make
    V D U S M Rk Features Laws Finite DL UL SL ML.
End FirstDiscovery.

Module FixedRank
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed)
  (Features : Restarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Rk := FixedRankDiscoveryOrder V Fixed.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
  Module Finite <: FINITE_DISCOVERY_ORDER_LAWS V Rk Laws :=
    FixedRankFiniteDiscoveryOrderLaws V Fixed FixedLaws.
  Include Make
    V D U S M Rk Features Laws Finite DL UL SL ML.
End FixedRank.

Module LeastSolution.

Module Make
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
End Make.

Module FiniteHeight
  (V : VAR) (D : DOMAIN) (S : SET V) (M : MAP V)
  (Rk : DISCOVERY_ORDER V) (Features : Restarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D) (FH : FINITE_HEIGHT_LAWS D DL)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module U := JoinUpdate V D.
  Module UL := JoinUpdateLaws V D DL FH.
  Module UBL := JoinUpdateUpperBoundLaws V D DL.
  Include Make
    V D U S M Rk Features RankLaws RankFinite DL UL UBL SL ML.
End FiniteHeight.

Module FirstDiscovery
  (V : VAR) (D : DOMAIN) (S : SET V) (M : MAP V)
  (Features : Restarting.FEATURES)
  (DL : DOMAIN_LAWS D) (FH : FINITE_HEIGHT_LAWS D DL)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Rk := ListDiscoveryOrder V.
  Module RankLaws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    ListDiscoveryOrderLaws V.
  Module RankFinite <: FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws :=
    ListFiniteDiscoveryOrderLaws V.
  Include FiniteHeight
    V D S M Rk Features RankLaws RankFinite DL FH SL ML.
End FirstDiscovery.

Module FixedRank
  (V : VAR) (D : DOMAIN) (S : SET V) (M : MAP V)
  (Fixed : STATELESS_RANK V) (FixedLaws : STATELESS_RANK_LAWS V Fixed)
  (Features : Restarting.FEATURES)
  (DL : DOMAIN_LAWS D) (FH : FINITE_HEIGHT_LAWS D DL)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Rk := FixedRankDiscoveryOrder V Fixed.
  Module RankLaws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
  Module RankFinite <: FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws :=
    FixedRankFiniteDiscoveryOrderLaws V Fixed FixedLaws.
  Include FiniteHeight
    V D S M Rk Features RankLaws RankFinite DL FH SL ML.
End FixedRank.

End LeastSolution.
