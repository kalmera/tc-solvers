# TC Solvers

Executable constraint solvers and constructive total-correctness proofs in Rocq,
with extracted OCaml libraries and specialized client adapters.

The initial version contains Simple, Restarting (four side-effect configurations),
and Narrowing Fixed Point. Each proves total correctness and finite-height join
leastness under its stated assumptions; Narrowing Fixed Point also proves a
narrowing-fixpoint result. See the [theorem map](docs/proofs.md).

## Use the OCaml libraries

With OCaml 5.4 and Dune 3.19 or newer in your environment:

```sh
make ocaml
# Or install the committed extraction in your current opam switch:
opam install .
```

The [examples](examples/) instantiate the extracted solver functors directly.
The libraries are `tc-solvers.extracted.slr.simple`,
`tc-solvers.extracted.slr.restarting`, and
`tc-solvers.extracted.slr.narrowing_fixed_point`.
[Extraction and client assumptions](docs/extraction.md) describe their contracts.

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

Sources are organized into `rocq/` (definitions and proofs), `ocaml/` (extraction,
runtime components, and adapters), `tests/`, and `examples/`. Generated OCaml is
committed and checked against regeneration in CI. Edit its generators instead.

MIT licensed; see [LICENSE](LICENSE).
