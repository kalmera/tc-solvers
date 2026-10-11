From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.dirty_read_restarting.DirtyReadRestarting.

Extraction Language OCaml.
Set Warnings "-extraction-opaque-accessed".
Module Engine := DirtyReadRestarting.Make.
Set Extraction Output Directory "ocaml/extracted".
Extraction "DirtyReadRestartingRuntime.ml" Engine.
