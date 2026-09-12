# Third-party components

The generic library cores in `ocaml/library/generated/` reuse extracted
callback control and the project's mutable adapter algorithms. They carry the
same extracted-code notices and license terms. They contain no Goblint code or
Batteries/Yojson runtime dependency; these packages are used only by adapter tests.

Rocq and Rocq Stdlib supply extracted support modules such as List and Nat.
Rocq Stdlib is LGPL-2.1. Their license notices are
included under `docs/licenses/`. OCaml's compiler and standard library are
external dependencies, as are Dune, Batteries, Yojson, and Goblint.

Goblint adapters implement Goblint interfaces; Goblint itself is not included.
The test helpers model only the frontend signatures used by the adapter checks.

The upstream source is Rocq Stdlib 9.1.0:
https://github.com/coq/stdlib/releases/tag/V9.1.0 . Its extracted support modules
retain copyright INRIA, CNRS, and contributors. The single-file narrowing runtime
also contains extracted Stdlib support. The generated code is derived from the
Rocq inputs with `ExtrOcamlBasic` and `ExtrOcamlNatInt` mappings.
