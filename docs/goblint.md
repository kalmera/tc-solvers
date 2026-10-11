# Goblint adapters

For the generic solver API, see the [`tc-solvers` library](library.md).

The `slr-paper` registration set preserves the paper's configuration:

| Identifier | Algorithm | Side reset | Dead-side elimination |
| --- | --- | --- | --- |
| `slrtc_s` | Simple | — | — |
| `slrtc_r` | Restarting | no | no |
| `slrtc_rs` | Restarting | yes | no |
| `slrtc_rd` | Restarting | no | yes |
| `slrtc_rds` | Restarting | yes | yes |
| `slrtc_n` | Narrowing Fixed Point | yes | yes |

The Restarting and Narrowing Fixed Point registrations enable controlled-owner
recomputation. Direct integrations can set either solver's `recompute_controlled`
flag to choose this behavior; reader wakeups and side-source repairs remain active.

All six use extracted callback control, the bitmap worklist, and `CopyUpdate`
(two copies followed by the widening/narrowing box).
`SLRTC_TRACE` is disabled by default.

```sh
python3 ocaml/adapters/goblint/install.py /path/to/analyzer --set slr-paper
make -C /path/to/analyzer release
```

The installer copies the six owned modules and backs up replaced files beneath
the analyzer's Git directory. Existing registrations outside this set remain in
place. Choose a checkout without conflicting duplicate registrations.

`make goblint-solvers` rebuilds proofs, extraction, and adapters.
`make goblint-adapters` reuses committed extraction. Generators and templates live
in `ocaml/adapters/goblint/`; their output is in its `generated/` directory.

For direct adapter integrations, `RANK_WORKLIST=bitmap`, `binary`, or `pqueue`
selects the worklist shared by all generated adapters. The paper installer
requires bitmap. The inlined variants and join updates support internal tests;
they introduce no extra registered solver names. Restore the default with
`make goblint-adapters RANK_WORKLIST=bitmap` before committing generated sources.

These adapters must satisfy the additional [implementation assumptions](extraction.md).

## Catching-up Plus Restarting (SLR-TC+) registrations

The catching-up registrations use `Slrtc_catching_up_update.DefaultUpdate`.
`slrtc_plus_restarting_no_side_reset_keep_dead_default` uses FIFO spawning
with controlled-owner recomputation disabled. The `_immediate` registration
disables FIFO spawning while preserving the other settings.
`slrtc_plus_restarting_no_side_reset_keep_dead_default_recompute_controlled` enables it
with FIFO-deferred spawning, side reset disabled, and dead-side elimination
disabled. The formal ordinary fixedness theorem uses OneBox updates; it does
not assert that this DefaultUpdate registration satisfies the OneBox theorem.

The historical `slrtc_dfr_...` identifiers remain compatibility aliases;
existing benchmark configurations and saved records keep their original names.

The Plus Restarting adapters expose `recompute_controlled` in their `FEATURES`
interface. Enabled adapters queue changed controlled owners for reevaluation
with the returned update phase, including when their RHS has no self-read.
Both extracted and inlined control forms implement the option.
