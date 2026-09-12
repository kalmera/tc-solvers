# TC Solvers

Executable constraint solvers and constructive total-correctness proofs in Rocq,
with a generic OCaml solver library, extracted reference versions, and Goblint adapters.

The initial version contains Simple, Restarting (four side-effect configurations),
and Narrowing Fixed Point. Each proves total correctness and finite-height join
leastness under its stated assumptions; Narrowing Fixed Point also proves a
narrowing-fixpoint result. See the [theorem map](docs/proofs.md).

## Use the generic library

`tc-solvers` provides generic callback solver functors with explicit update policies.
See the [library guide](docs/library.md) and [examples](examples/library/).
With OCaml 5.4 and Dune 3.19 or newer:

```sh
make ocaml
# Or install the libraries in your current opam switch:
opam install .
```

The [extracted reference libraries](docs/extraction.md) and their
[examples](examples/) are also available for testing.

## Check the proofs and regenerate

Validated with OCaml 5.4.0, Rocq 9.1.1, Stdlib 9.1.0, and Dune 3.23.1.
Use any opam switch with these dependencies; its name is unrestricted.

```sh
opam install rocq-core.9.1.1 rocq-stdlib.9.1.0 dune.3.23.1 batteries.3.11.0 yojson.3.0.0
opam exec -- make
```

`make` compiles proofs, regenerates extraction and adapters, and runs the existing
OCaml smoke and differential checks. `make proofs`, `make narrowing-fixed-point`,
`make regenerate`, and `make test` select individual stages. Set `ROCQ_JOBS=1`
for sequential proof compilation.

## Integrate with Goblint

The [Goblint guide](docs/goblint.md) covers the six `slrtc_*` registrations,
generation, installation, and backend selection.

Sources are organized into `rocq/` (definitions and proofs), `ocaml/` (the generic
library, extracted references, runtime components, and adapters), `tests/`, and `examples/`. Generated OCaml is
committed and checked against regeneration in CI. Edit its generators instead.

MIT licensed; see [LICENSE](LICENSE).
