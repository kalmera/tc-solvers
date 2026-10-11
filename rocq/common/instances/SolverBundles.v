From TcSolvers Require Export common.SolverParameters common.instances.Chain.
From TcSolvers Require Import common.FiniteHeight common.ReluctantUpdate.

(** Policies shared by finite-height instances of every solver. *)
Module FiniteHeightParameters
  (PV : VAR) (PD : DOMAIN) (PS : SET PV) (PM : MAP PV)
  (F : RESTARTING_FEATURES) (PDL : DOMAIN_LAWS PD)
  (Height : FINITE_HEIGHT_LAWS PD PDL)
  (PSL : SET_LAWS PV PS) (PML : MAP_LAWS PV PM).
  Module V := PV.
  Module D := PD.
  Module S := PS.
  Module M := PM.
  Module Features := F.
  Module DL := PDL.
  Module SL := PSL.
  Module ML := PML.
  Module Rk := ListDiscoveryOrder V.
  Module RankLaws := ListDiscoveryOrderLaws V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws V.
  Module U := JoinUpdate V D.
  Module UL := JoinUpdateLaws V D DL Height.
  Module UBL := JoinUpdateUpperBoundLaws V D DL.
  Module OUL := OrdinaryUpdateTerminationAdapter V D U UL.
  Module Covered <: COVERED_JOIN_CREDIT_LAWS V D U UL.
    Lemma covered_join_nonincreasing : forall target phase old input aggregate,
      D.leq old aggregate = true ->
      D.leq input old = false -> D.leq input aggregate = true ->
      UL.remaining_changes (fst (U.update true target phase old input))
        (D.join old input) <= UL.remaining_changes phase old.
    Proof.
      intros target phase old input aggregate Hold Hgrow Hcovered.
      exact (UL.remaining_changes_nonincreasing true target phase old input).
    Qed.
  End Covered.
  Module SU := ReluctantSideUpdate V D U.
  Module SUL := ReluctantRestartingSideUpdateTerminationLaws V D U DL UL Covered.
  Module ASUL := ReluctantSideUpdateTerminationLaws V D U DL UL Covered.
  Module OSL := OUL.
  Module SSL := SUL.
  Module SUBL := ReluctantSideUpdateUpperBoundLaws V D U DL UBL.
End FiniteHeightParameters.

(** One bundle also supplies Chain's widening/narrowing laws and policies. *)
Module ChainParameters (F : RESTARTING_FEATURES) <: COMPLETE_PARAMETERS.
  Module E := Chain.
  Include FiniteHeightParameters E.V E.D E.S E.M F E.DL E.Height E.SL E.ML.
  Module WN := E.WN.
  Module WNL := E.WNL.
  Module WS := E.WS.
  Module FixedU := OneBoxUpdate V D WN.
  Module FixedUL := E.UpdateLaws FixedU.
  Module FixedSU := ReluctantSideUpdate V D FixedU.
  Module FixedSUL := ReluctantSideUpdateSoundLaws V D FixedU DL FixedUL.
End ChainParameters.
