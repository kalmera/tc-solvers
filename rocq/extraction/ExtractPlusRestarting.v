From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.plus_restarting.PlusRestarting.

Extraction Language OCaml.
Set Warnings "-extraction-opaque-accessed".
Module Engine := PlusRestarting.Make.
Set Extraction Output Directory "ocaml/extracted".
Extraction "PlusRestartingRuntime.ml" Engine.
