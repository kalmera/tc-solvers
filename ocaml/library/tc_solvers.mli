(* Generic mutable callback solvers. See the installed library guide for
    domain/update laws and callback obligations. *)
include module type of Interfaces
module Update = Update
module Slr = Slr
