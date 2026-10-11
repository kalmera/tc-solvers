From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.deferred_simple.DeferredSimple.

Extraction Language OCaml.
Set Warnings "-extraction-opaque-accessed".
Module Engine := DeferredSimple.Make.
Set Extraction Output Directory "ocaml/extracted".
Extraction "DeferredSimpleRuntime.ml" Engine.
