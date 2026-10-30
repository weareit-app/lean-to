# Architecture decisions

The one record of this repository's decisions, newest last within each section. Changing an agreed choice in `AGENTS.md` adds a dated entry here.

## Starting point

Decided when the repository was generated (see its first commit).

- Visibility: public.
- Licence. Repository: Apache-2.0.
- Lean `leanprover/lean4:v4.35.0` with Mathlib `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), the factory's verified pair. Lean files use the module system (`module`, `public import`). Upgrading Lean or Mathlib is an explicit change made in this repository.
- Depends on pinned Mathlib only; never on private research or learn-it.
- Decisions live in this file; `docs/adr/` is not used, and `tools/decision-records/check-no-adr-folder.mjs` fails if it exists.

## Library

- 2026-10-30: First library content, from the first construction (`ct-research/deep/first-construction/`). `LeanTo.RelationAlgebra` holds Boolean-valued relations on finite types, relation-algebra expressions with closure, and automorphism invariance (nondefinability and obstruction soundness). `LeanTo.Interface` holds interfaces in bundle form over fixed positions, preserving refinements and commitments with their composition theorems, translation of queries along a refinement, the `Accept` predicate, merges of independent refinements (fiberwise pullback, exactness criterion, and the pushout in `(Over Q)ᵒᵖ`), and extensions that add positions. The skeleton `LeanTo/Basic.lean` is removed. Relations are Boolean-valued rather than Mathlib's `SetRel` so that every concrete check closes by `decide`; translation enumerates answers with `FinEnum`, because `Finset.toList` is noncomputable.
