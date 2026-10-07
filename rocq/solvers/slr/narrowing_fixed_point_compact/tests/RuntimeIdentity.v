From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain common.FiniteHeight common.Assumptions
  solvers.slr.common.DiscoveryOrder
  solvers.slr.narrowing_fixed_point.NarrowingFixedPoint
  solvers.slr.narrowing_fixed_point_compact.NarrowingFixedPoint.
Import ListNotations.

(** The reference proof stack is used only here, to certify the extracted
    runtime definitions. The new generic proof unit never imports it. *)
Module RuntimeIdentity (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Reference := TcSolvers.solvers.slr.narrowing_fixed_point.NarrowingFixedPoint.Make
    V D U S M Features DL UL SL ML.
  Module R := Reference.R.
  Module Ranks := ListDiscoveryOrder V.
  Module Copy := NarrowingFixedPoint.WithCore V D U S M Ranks Features R.
  Theorem next_config_identical tf c : Copy.next_config tf c = Reference.next_config tf c.
  Proof. reflexivity. Qed.
  Theorem run_fuel_identical fuel tf c : Copy.run_fuel fuel tf c = Reference.run_fuel fuel tf c.
  Proof. reflexivity. Qed.
  Theorem solve_fuel_identical fuel tf roots : Copy.solve_fuel fuel tf roots = Reference.solve_fuel fuel tf roots.
  Proof. reflexivity. Qed.
End RuntimeIdentity.

Module E := Chain.
Module Identity := RuntimeIdentity E.V E.D E.U E.S E.M Base.AllEnabledFeatures E.DL E.UL E.SL E.ML.
Print Assumptions Identity.next_config_identical.
Print Assumptions Identity.solve_fuel_identical.
