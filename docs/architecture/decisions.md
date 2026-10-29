# Architecture decisions

The one record of this repository's decisions, newest last within each section. Changing an agreed choice in `AGENTS.md` adds a dated entry here.

## Starting point

Decided when the repository was generated (see its first commit).

- Visibility: public.
- Licence. Repository: Apache-2.0.
- Lean `leanprover/lean4:v4.35.0` with Mathlib `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), the factory's verified pair. Lean files use the module system (`module`, `public import`). Upgrading Lean or Mathlib is an explicit change made in this repository.
- Depends on pinned Mathlib only; never on private research or learn-it.
- Decisions live in this file; `docs/adr/` is not used, and `tools/decision-records/check-no-adr-folder.mjs` fails if it exists.

## Changes

- 2026-10-28. Issue tracker: GitHub Issues on `weareit-app/lean-to`, replacing local Markdown under `.scratch/`. The five default triage labels exist on the repository. See `docs/agents/issue-tracker.md`.
- 2026-10-28. Tests: a `LeanToTest` library, a default Lake target, so `lake build` (and so `./scripts/check.sh` and CI) compiles it. Test modules import `LeanTo` only, as a client would, and pin each new declaration's axioms with `#guard_msgs in #print axioms`.
- 2026-10-28. Naming: lemmas about Mathlib's types go in Mathlib's own namespaces (for example `SetRel`) with Mathlib-style names, so they can be upstreamed unchanged. If a Mathlib upgrade adds the same name, the build fails; delete the local copy then.
- 2026-10-28. The skeleton `LeanTo/Basic.lean` is retired, as its docstring asked, now that `LeanTo/Relation/FunctionGraph.lean` is the first real module.
- 2026-10-28. Membership lemmas `SetRel.mem_graph_comp` and `SetRel.mem_comp_inv_graph` are not `@[simp]`, departing from ticket #2 of spec #1: `simp` already proves them from Mathlib's simp set, so the tag would fail Mathlib's simpNF linter and block upstreaming. They are for `rw`.
