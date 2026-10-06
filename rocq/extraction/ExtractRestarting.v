From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.restarting.Restarting.

Extraction Language OCaml.
Set Extraction Output Directory "ocaml/extracted".
Set Warnings "-extraction-opaque-accessed".

(** Extract the first-discovery instance of the policy-parametric Restarting
    solver. Extraction preserves the three compile-time feature constants. *)
Recursive Extraction Library Restarting.
