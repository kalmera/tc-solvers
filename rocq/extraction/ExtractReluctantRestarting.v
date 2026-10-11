From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.reluctant_restarting.ReluctantRestarting.

Extraction Language OCaml.
Set Warnings "-extraction-opaque-accessed".
Module Engine := ReluctantRestarting.Make.
Set Extraction Output Directory "ocaml/extracted".
Extraction "ReluctantRestartingRuntime.ml" Engine.
