From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.dormant_restarting.DormantRestarting.

Extraction Language OCaml.
Set Warnings "-extraction-opaque-accessed".
Module Engine := DormantRestarting.Make.
Set Extraction Output Directory "ocaml/extracted".
Extraction "DormantRestartingRuntime.ml" Engine.
