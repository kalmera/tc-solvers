From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.narrowing_fixed_point.NarrowingFixedPoint.
Extraction Language OCaml.
Set Warnings "-extraction-opaque-accessed".
Module Solver := NarrowingFixedPoint.Make.
Set Extraction Output Directory "ocaml/extracted".
Extraction "NarrowingFixedPointRuntime.ml" Solver.
