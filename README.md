# lean-to

General-purpose, Mathlib-compatible definitions and theorems, potentially upstreamable.

Status: early. The first module, `LeanTo.Relation.FunctionGraph`, proves that composing a relation with a function's graph is substitution, in Mathlib's `SetRel` representation: on either side, on both sides (restriction), and that a graph is left adjoint to its converse. These are the relational shadows of companions, conjoints and restriction in a double category; no double-category structure is formalized yet. What Mathlib already covers, and what is still missing, is in [the gap audit](docs/audits/function-graphs-and-relational-composition.md).

Use it from another Lake package by requiring `lean_to` and writing `import LeanTo`. Tests live in `LeanToTest` and are built by `lake build`.

## Getting started

```sh
lake exe cache get
./scripts/check.sh
```

`./scripts/check.sh` runs `lake build` and the skills-sync and decision-record checks (Node 24 runs the last two).

## Licence

- Repository: Apache-2.0.
