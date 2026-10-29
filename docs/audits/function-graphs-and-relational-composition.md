# Gap audit: function graphs and relational composition

What the pinned Mathlib already provides for a function's graph, relational composition and substitution, what `lean-to` adds, and what a double-category reading of companions and conjoints still needs. Spec: [weareit-app/lean-to#1](https://github.com/weareit-app/lean-to/issues/1).

## Pins and method

- Lean `leanprover/lean4:v4.35.0`; Mathlib `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (from `lake-manifest.json`). Inspected 2026-10-28.
- Inspected scope: the pinned Mathlib tree under `.lake/packages/mathlib/Mathlib`, and this repository. Not inspected: other Lean repositories, public or private. A miss below therefore means **not located in inspected scope**, not absent.
- Name searches, run from the Mathlib package root:

  ```text
  grep -rn 'fun_eq_comp\|comp_eq_fun\|bicompl' Mathlib
  grep -rn 'def graph\|graph_comp\|graph.*inv\|inv.*graph\|\.graph ○\|○ .*\.graph' Mathlib
  grep -rn 'DoubleCategory\|FramedBicategory\|Equipment\|Companion\|Conjoint\|CartesianCell' Mathlib
  ls Mathlib/CategoryTheory | grep -i 'double\|equip\|framed'
  ```

- Type checks: each candidate statement was elaborated against the pinned Mathlib (`lake env lean`) before it was proved; the new names were unknown constants, and `simp` alone closes the membership forms (so they are not tagged `@[simp]`). Statement shapes, not only names, were compared with the matches below.

## Orientation conventions

| Notation | Declaration | Order | Meaning |
| --- | --- | --- | --- |
| `r ∘r p` (local) | `Relation.Comp` | diagrammatic | `∃ b, r a b ∧ p b c` |
| `R ○ S` (scoped `SetRel`) | `SetRel.comp` | diagrammatic | `∃ b, a ~[R] b ∧ b ~[S] c` |
| `f ∘ g` | `Function.comp` | applicative | `f (g x)` |
| `₍f₎B ⊙ M ⊙ D₍g₎` | Shulman, Theorem 4.1 | diagrammatic | `A ⇸ B ⇸ D ⇸ C` |

So `Function.graph_comp : graph (f ∘ g) = graph g ○ graph f`, and `f.graph ○ R` means "apply `f`, then `R`". Shulman's companion `₍f₎B : A ⇸ B` corresponds to `f.graph`, and his conjoint `B₍f₎ : B ⇸ A` to `f.graph.inv`. Mathlib's Prop-valued right-hand lemma composes with `(· = g ·)`, which is the conjoint `g.graph.inv` in Prop-valued form.

## What already exists

### Function as relation

| Declaration | Type | Source |
| --- | --- | --- |
| `Function.graph` | `(α → β) → SetRel α β`, `{(a, b) \| f a = b}` | `Mathlib/Basic/Rel.lean:567` |
| `Function.mem_graph` | `a ~[f.graph] b ↔ f a = b` (simp) | `Mathlib/Basic/Rel.lean:569` |
| `Function.graph_injective` | `Injective graph` | `Mathlib/Basic/Rel.lean:571` |
| `Function.graph_id` | `graph id = SetRel.id` | `Mathlib/Basic/Rel.lean:576` |
| `SetRel.exists_graph_eq_iff` | `(∃! f, graph f = R) ↔ ∀ a, ∃! b, a ~[R] b` | `Mathlib/Basic/Rel.lean:589` |
| `Equiv.graph_inv` | `(f.symm).graph = (f : α → β).graph.inv` for `f : α ≃ β` | `Mathlib/Basic/Rel.lean:586` |
| `SetRel` | `abbrev SetRel α β := Set (α × β)` | `Mathlib/Basic/Rel.lean:68` |
| `Rel` | `abbrev Rel (α β : Sort*) : Sort _ := α → β → Prop` | `Mathlib/Basic/Rel.lean:610` |

Verdict: **already formalized**.

### Relational composition

| Declaration | Type | Source |
| --- | --- | --- |
| `Relation.Comp` | `(α → β → Prop) → (β → γ → Prop) → α → γ → Prop` | `Mathlib/Logic/Relation.lean:144` |
| `Relation.comp_assoc` | `(r ∘r p) ∘r q = r ∘r p ∘r q` | `Mathlib/Logic/Relation.lean:174` |
| `Relation.flip_comp` | `flip (r ∘r p) = flip p ∘r flip r` | `Mathlib/Logic/Relation.lean:177` |
| `SetRel.comp`, `○` | `SetRel α β → SetRel β γ → SetRel α γ` | `Mathlib/Basic/Rel.lean:150`, `:152` |
| `SetRel.mem_comp` | `a ~[R ○ S] c ↔ ∃ b, a ~[R] b ∧ b ~[S] c` | `Mathlib/Basic/Rel.lean:154` |
| `SetRel.comp_assoc`, `SetRel.inv_comp` | associativity; `(R ○ S).inv = S.inv ○ R.inv` | `Mathlib/Basic/Rel.lean:158`, `:164` |
| `Function.graph_comp` | `graph (f ∘ g) = graph g ○ graph f` | `Mathlib/Basic/Rel.lean:578` |
| `CategoryTheory.RelCat` | category of types and `SetRel`s, `f ≫ g` is `f.rel ○ g.rel` | `Mathlib/CategoryTheory/Category/RelCat.lean:33`, `:54` |
| `CategoryTheory.RelCat.graphFunctor` | `Type u ⥤ RelCat`, faithful, essentially surjective | `Mathlib/CategoryTheory/Category/RelCat.lean:74` |
| `CategoryTheory.RelCat.rel_iso_iff` | isomorphisms of `RelCat` are graphs of bijections | `Mathlib/CategoryTheory/Category/RelCat.lean:89` |

`SetRel.comp` and `Relation.Comp` agree definitionally on membership (`Iff.rfl`, tested). Verdict: **already formalized**.

### Composition with a graph is substitution

| Declaration | Type | Source |
| --- | --- | --- |
| `Relation.fun_eq_comp` | `(f · = ·) ∘r r = (r <| f ·)` (simp) | `Mathlib/Logic/Relation.lean:159` |
| `Relation.comp_eq_fun` | `r ∘r (· = f ·) = (r · <| f ·)` (simp) | `Mathlib/Logic/Relation.lean:151` |
| `Set.image_eq`, `Set.preimage_eq` | image and preimage of `f` are those of `f.graph` | `Mathlib/Basic/Rel.lean:596`, `:599` |

For Prop-valued relations: **already formalized**, on both sides. `Relation.fun_eq_comp` is Mathlib's; the pointwise statement `Relation.Comp (fun x y => f x = y) r a c ↔ r (f a) c` is one `rw` of it (tested). It is a good learner exercise and regression check, and must not be presented as a new result.

For `Function.graph` and `SetRel.comp`: **not located in inspected scope**. No lemma rewrites `f.graph ○ R` or `R ○ g.graph.inv`. `lean-to` adds them (below).

### Restriction and extension

| Declaration | Type | Source |
| --- | --- | --- |
| `Function.bicompl` | `bicompl m f g a c = m (f a) (g c)` | `Mathlib/Logic/Function/Defs.lean:186` |
| `Relation.Map` | `Map r f g c d ↔ ∃ a b, r a b ∧ f a = c ∧ g b = d` | `Mathlib/Logic/Relation.lean:222` |
| `Relation.map_le_iff_le_bicompl` | `Map r f g ≤ s ↔ r ≤ s.bicompl f g` | `Mathlib/Logic/Relation.lean:297` |
| `gc_map_bicompl` | `GaloisConnection (Relation.Map · f g) (·.bicompl f g)` | `Mathlib/Order/GaloisConnection/Basic.lean:452` |
| `SetRel.restrictDomain` | restriction of the domain to a subtype | `Mathlib/Basic/Rel.lean:353` |

Restriction along two functions is `Function.bicompl` (Prop-valued) or preimage under `Prod.map f g` (`SetRel`), and extension ⊣ restriction is `gc_map_bicompl`. No lemma says restriction *is* composition with a graph and a converse graph in either representation; for Prop-valued relations it follows by rewriting with `fun_eq_comp` and `comp_eq_fun` (tested). Verdict: **partial infrastructure**.

### Graph ⊣ converse

`Bicategory.Adjunction` exists (`Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:89`), but `RelCat` is only a 1-category; no bicategory or locally ordered structure on relations was located. No lemma states `SetRel.id ⊆ f.graph ○ f.graph.inv` or `f.graph.inv ○ f.graph ⊆ SetRel.id`. Verdict: **not located in inspected scope**.

### Double categories, companions, conjoints

The searches above find no `DoubleCategory`, `FramedBicategory`, equipment, companion/conjoint (the only hits, in four files, are docstrings using "Companion" in its ordinary sense, as in "Companion lemma"), or `CartesianCell`, and no matching directory under `Mathlib/CategoryTheory`. What exists nearby: profunctors (`Mathlib/CategoryTheory/Profunctor/`: `Functor.toProfunctor`, `Profunctor.whiskerLeft₂`, `Profunctor.comp`), the bicategory `ProfCat` (`Mathlib/CategoryTheory/Profunctor/Bicategory.lean:92`), bicategorical adjunctions and mates, and `Bicategory/Span`. Verdict: **not located in inspected scope**; other Lean repositories were not inspected.

## What `lean-to` adds

All in `LeanTo/Relation/FunctionGraph.lean`, in Mathlib's `SetRel` namespace so they can be upstreamed unchanged. None is a definition. Names read `g.graph.inv` as `inv_graph`, outer symbol first, as Mathlib's `SetRel.inv_comp` does for `(R ○ S).inv`; `Equiv.graph_inv` names a different shape, the graph of an inverse. The membership forms are not `@[simp]`: `simp` already proves them from `SetRel.mem_comp`, `Function.mem_graph` and `SetRel.mem_inv`, so the tag would fail Mathlib's simpNF linter.

| Declaration | Statement | Nearest Mathlib result, and why this is not a duplicate | Axioms |
| --- | --- | --- | --- |
| `SetRel.graph_comp_eq_preimage` | `f.graph ○ R = Prod.map f id ⁻¹' R` | `Relation.fun_eq_comp`, Prop-valued only | `propext`, `Quot.sound` |
| `SetRel.mem_graph_comp` | `a ~[f.graph ○ R] c ↔ f a ~[R] c` | as above; pointwise form for `rw` | `propext`, `Quot.sound` |
| `SetRel.comp_inv_graph_eq_preimage` | `R ○ g.graph.inv = Prod.map id g ⁻¹' R` | `Relation.comp_eq_fun`, Prop-valued only | `propext`, `Quot.sound` |
| `SetRel.mem_comp_inv_graph` | `a ~[R ○ g.graph.inv] c ↔ a ~[R] g c` | as above | `propext`, `Quot.sound` |
| `SetRel.graph_comp_comp_inv_graph` | `f.graph ○ M ○ g.graph.inv = Prod.map f g ⁻¹' M` | `Function.bicompl` names the right side; nothing connects it to composition | `propext`, `Quot.sound` |
| `SetRel.id_subset_graph_comp_inv_graph` | `SetRel.id ⊆ f.graph ○ f.graph.inv` | `SetRel.id_subset` and `SetRel.id_subset_iff` (`Mathlib/Basic/Rel.lean:369`, `:371`) give `.id ⊆ R` from `R.IsRefl`, but no `IsRefl` instance for `f.graph ○ f.graph.inv` exists | none |
| `SetRel.inv_graph_comp_graph_subset_id` | `f.graph.inv ○ f.graph ⊆ SetRel.id` | none located | none |

The axiom sets are pinned with `#guard_msgs` in `LeanToTest/Relation/FunctionGraph.lean`, which imports `LeanTo` only and is built by `lake build`. That file also walks the elementary development (function as relation, composition with a graph, substitution, restriction) using the Mathlib declarations above.

## What a companion/conjoint interpretation still needs

The relational facts above are what companions and conjoints *become* in the double category of relations. They do not formalize companions or conjoints. That double category is thin: a cell from `N : SetRel α γ` to `M : SetRel β δ` with vertical boundaries `f`, `g` is the proposition `N ⊆ Prod.map f g ⁻¹' M`. So the binding cells exist trivially, Shulman's equations (4.3)–(4.4) hold by proof irrelevance, and the cartesian factorisation through the restriction is `Iff.rfl` (tested, with that caveat). None of this is evidence for Theorem 4.1, where cells carry data.

To state and prove Theorem 4.1 (iii) ⇒ (i) of Shulman, *Framed Bicategories and Monoidal Fibrations* (arXiv:0706.1286v2, printed pp. 15–17), the following are still needed. The labels T0–T7 follow the prove.how experiment plan; **all are open**:

1. **T0** A pseudo double category interface: objects, vertical category, horizontal arrows with composition `⊙` and units, cells with four boundaries, vertical and horizontal pasting, and associator/unitor isomorphisms that are globular cells satisfying coherence. Either a definition, or a justified strictification with the general case recovered.
2. **T1** Companion and conjoint data for a vertical arrow `f`: horizontal arrows `₍f₎B`, `B₍f₎` and the four binding cells, with equations (4.3) and (4.4) as stated hypotheses.
3. **T2–T4** The composite `₍f₎B ⊙ M ⊙ D₍g₎` (with the associator fixed), the comparison cell of (4.5) with boundaries `(f, g)`, and the factorisation constructor of (4.6) for an arbitrary cell with boundaries `(f ∘ h, g ∘ k)`.
4. **T5–T7** Existence and uniqueness of the factorisation, packaged as a cartesian cell, with fidelity review against the printed statement.
5. **An instance** turning types, functions and `SetRel` into such a double category, so that this file's lemmas become a worked example of the abstract interface rather than a parallel one. Mathlib also lacks the locally ordered 2-category of relations that would let `f.graph ⊣ f.graph.inv` be stated as a `Bicategory.Adjunction`.

The profunctor specialisation (representables composed with `K` as `K.whiskerLeft₂ F G`) is a separate, optional result and does not substitute for T7.

## Reuse

- **`learn-to-prove-it` can reuse**: `Relation.fun_eq_comp` and `Relation.comp_eq_fun` directly from Mathlib, for the Prop-valued exercise (the pointwise form is one `rw` of the former); and, by depending on `lean-to`, the `SetRel` lemmas above for exercises phrased with `Function.graph`, restriction and the unit/counit of graph ⊣ converse. The concrete `ℕ` examples in the test file are checkable instances an exercise generator could vary.
- **Left for the research formalization**: everything in the previous section. The elementary development here is a learner exercise and regression check, not a step of the Theorem 4.1 proof.
