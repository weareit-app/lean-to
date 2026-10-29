/-
Copyright (c) 2026 Josh Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Smith
-/
module

public import Mathlib.Basic.Rel

/-!
# Composing relations with the graph of a function

`Function.graph f : SetRel α β` is the relation `{(a, b) | f a = b}`. This file proves that
composing with a graph is substitution, in the set-of-pairs representation `SetRel`, on either
side; that composing on both sides is restriction; and that a graph is left adjoint to its converse
in the ordered category of relations.

These are the relational shadows of companions (`f.graph`), conjoints (`f.graph.inv`) and
restriction in a double category. No double-category structure is defined here.

## Orientation

`SetRel.comp` is diagrammatic: `a ~[R ○ S] c ↔ ∃ b, a ~[R] b ∧ b ~[S] c`, so `f.graph ○ R` means
"apply `f`, then `R`". Compare `Function.graph_comp : graph (f ∘ g) = graph g ○ graph f`.

## Relation to Mathlib

The Prop-valued counterparts already exist in Mathlib and are not restated here:
`Relation.fun_eq_comp : (f · = ·) ∘r r = (r <| f ·)` and
`Relation.comp_eq_fun : r ∘r (· = f ·) = (r · <| f ·)` in `Mathlib.Logic.Relation`.
The pinned Mathlib has no `SetRel` form for `Function.graph`; that gap is what this file fills.
See `docs/audits/function-graphs-and-relational-composition.md`.
-/

@[expose] public section

open scoped SetRel

variable {α β γ : Type*}

namespace SetRel

/-- Following the graph of `f` by `R` is `R` with `f` substituted in its first argument. -/
theorem graph_comp_eq_preimage (f : α → β) (R : SetRel β γ) :
    f.graph ○ R = Prod.map f id ⁻¹' R := by
  ext ⟨a, c⟩
  simp

/-- Pointwise form of `SetRel.graph_comp_eq_preimage`. Not `@[simp]`: `simp` already proves it
from `SetRel.mem_comp` and `Function.mem_graph`. -/
theorem mem_graph_comp {f : α → β} {R : SetRel β γ} {a : α} {c : γ} :
    a ~[f.graph ○ R] c ↔ f a ~[R] c := by
  simp [graph_comp_eq_preimage]

/-- Following `R` by the converse of the graph of `g` is `R` with `g` substituted in its second
argument. -/
theorem comp_inv_graph_eq_preimage (R : SetRel α β) (g : γ → β) :
    R ○ g.graph.inv = Prod.map id g ⁻¹' R := by
  ext ⟨a, c⟩
  simp

/-- Pointwise form of `SetRel.comp_inv_graph_eq_preimage`. Not `@[simp]`, for the same reason
as `SetRel.mem_graph_comp`. -/
theorem mem_comp_inv_graph {R : SetRel α β} {g : γ → β} {a : α} {c : γ} :
    a ~[R ○ g.graph.inv] c ↔ a ~[R] g c := by
  simp [comp_inv_graph_eq_preimage]

/-- Restriction of `M` along two functions: the graph of `f`, then `M`, then the converse of the
graph of `g`, is `M` with `f` and `g` substituted. In Shulman's notation for a double category this
is the relational case of `₍f₎B ⊙ M ⊙ D₍g₎`. Compare `Function.bicompl` for Prop-valued
relations. -/
theorem graph_comp_comp_inv_graph {δ : Type*} (f : α → β) (M : SetRel β δ) (g : γ → δ) :
    f.graph ○ M ○ g.graph.inv = Prod.map f g ⁻¹' M := by
  ext ⟨a, c⟩
  simp

/-- Unit of the adjunction `f.graph ⊣ f.graph.inv`: going along `f` and back relates every
point to itself. -/
theorem id_subset_graph_comp_inv_graph (f : α → β) : .id ⊆ f.graph ○ f.graph.inv := by
  rintro ⟨a, _⟩ rfl
  exact ⟨f a, rfl, rfl⟩

/-- Counit of the adjunction `f.graph ⊣ f.graph.inv`: going back along `f` and forward again
relates only equal points. -/
theorem inv_graph_comp_graph_subset_id (f : α → β) : f.graph.inv ○ f.graph ⊆ .id := by
  rintro ⟨b, b'⟩ ⟨a, hb, hb'⟩
  exact hb.symm.trans hb'

end SetRel
