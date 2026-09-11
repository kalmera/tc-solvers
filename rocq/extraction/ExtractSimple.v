From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TcSolvers Require Import solvers.slr.simple.Simple.

Extraction Language OCaml.
Set Extraction Output Directory "ocaml/extracted".
Set Warnings "-extraction-opaque-accessed".

(** Extract the first-discovery instance of the policy-parametric Simple
    solver.  The fixed-rank instance is primarily a theory-side view. *)
Recursive Extraction Library Simple.
