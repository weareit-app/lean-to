module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs

/-!
# Decidable binary relations on a finite type

Boolean-valued binary relations on a type, with the operations of a relation algebra that need
a finite carrier: identity, relational composition, and bounded reflexive–transitive closure.
Boolean values keep every concrete relation decidable, so finite checks close by `decide`.

## Main definitions

* `LeanTo.BoolRel α`: a Boolean-valued binary relation on `α`.
* `LeanTo.BoolRel.idRel`, `LeanTo.BoolRel.comp`: identity and composition.
* `LeanTo.BoolRel.iterClosure n R`: paths of `R` of length at most `n`.
* `LeanTo.BoolRel.closure R`: `iterClosure (Fintype.card α) R`.
* `LeanTo.BoolRel.IsInvariant σ R`: the permutation `σ` preserves `R`.

## Main results

* `LeanTo.BoolRel.isInvariant_idRel`, `isInvariant_comp`, `isInvariant_iterClosure`:
  identity, composition and bounded closure commute with relabeling by a permutation.
-/

@[expose] public section

namespace LeanTo

universe u

/-- A Boolean-valued binary relation on `α`. -/
abbrev BoolRel (α : Type u) := α → α → Bool

namespace BoolRel

variable {α : Type u}

/-- The identity relation. -/
def idRel [DecidableEq α] : BoolRel α := fun x y ↦ decide (x = y)

/-- Relational composition: `comp R S x z` when some `y` has `R x y` and `S y z`. -/
def comp [Fintype α] (R S : BoolRel α) : BoolRel α :=
  fun x z ↦ decide (∃ y, (R x y && S y z) = true)

/-- `iterClosure n R` relates `x` to `y` when an `R`-path of length at most `n` joins them. -/
def iterClosure [DecidableEq α] [Fintype α] : ℕ → BoolRel α → BoolRel α
  | 0, _ => idRel
  | n + 1, R => fun x y ↦ idRel x y || comp R (iterClosure n R) x y

/-- Reflexive–transitive closure on a finite carrier, computed as paths of length at most the
number of elements. -/
def closure [DecidableEq α] [Fintype α] (R : BoolRel α) : BoolRel α :=
  iterClosure (Fintype.card α) R

/-- The permutation `σ` preserves the relation `R`: relabeling both arguments by `σ` does not
change its value. -/
def IsInvariant (σ : Equiv.Perm α) (R : BoolRel α) : Prop := ∀ x y, R (σ x) (σ y) = R x y

instance [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (R : BoolRel α) :
    Decidable (IsInvariant σ R) :=
  inferInstanceAs (Decidable (∀ x y, R (σ x) (σ y) = R x y))

/-- Every permutation preserves the identity relation. -/
theorem isInvariant_idRel [DecidableEq α] (σ : Equiv.Perm α) : IsInvariant σ (idRel (α := α)) :=
  fun x y ↦ by simp [idRel, σ.injective.eq_iff]

/-- A permutation that preserves `R` and `S` preserves their composition. -/
theorem isInvariant_comp [Fintype α] {σ : Equiv.Perm α} {R S : BoolRel α}
    (hR : IsInvariant σ R) (hS : IsInvariant σ S) : IsInvariant σ (comp R S) := by
  intro x z
  simp only [comp, decide_eq_decide]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨σ.symm y, ?_⟩
    rwa [← hR, ← hS, σ.apply_symm_apply]
  · rintro ⟨y, hy⟩
    exact ⟨σ y, by rwa [hR, hS]⟩

/-- A permutation that preserves `R` preserves its bounded closures. -/
theorem isInvariant_iterClosure [DecidableEq α] [Fintype α] {σ : Equiv.Perm α} {R : BoolRel α}
    (hR : IsInvariant σ R) : ∀ n, IsInvariant σ (iterClosure n R)
  | 0 => isInvariant_idRel σ
  | n + 1 => fun x y ↦ by
    simp only [iterClosure, isInvariant_idRel σ x y,
      isInvariant_comp hR (isInvariant_iterClosure hR n) x y]

/-- A permutation that preserves `R` preserves its reflexive–transitive closure. -/
theorem isInvariant_closure [DecidableEq α] [Fintype α] {σ : Equiv.Perm α} {R : BoolRel α}
    (hR : IsInvariant σ R) : IsInvariant σ (closure R) :=
  isInvariant_iterClosure hR _

end BoolRel

end LeanTo
