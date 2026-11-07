module

public import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Functors and the cocartesian monoidal structure

Give categories with an initial object and binary coproducts the cocartesian monoidal structure
`(⨿, ⊥_)`: Mathlib's `monoidalOfHasFiniteCoproducts` and `symmetricOfHasFiniteCoproducts`, used
here as local instances. This file is the cocartesian counterpart of
`Functor.OplaxMonoidal.ofChosenFiniteProducts`, `Functor.Monoidal.ofChosenFiniteProducts` and
`Functor.Braided.ofChosenFiniteProducts`
(`Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean`).

## Main definitions

* `Functor.LaxMonoidal.ofHasFiniteCoproducts F`: every functor is lax monoidal, with
  `ε = initialComparison F` and `μ X Y = coprodComparison F X Y`.
* `Functor.Monoidal.ofHasFiniteCoproducts F`: if `F` preserves finite coproducts, these maps are
  isomorphisms, so `F` is monoidal.
* `Functor.Braided.ofHasFiniteCoproducts F`: such an `F` is braided.

None of these is an instance: as for the cartesian versions, an instance would create a diamond
for the identity and for composites of functors.

## Implementation notes

Mathlib has no cocartesian analogue of `CartesianMonoidalCategory` (see the TODO in
`Mathlib/CategoryTheory/Monoidal/OfHasFiniteProducts.lean`), so the monoidal structure is the one
Mathlib puts on a category with finite coproducts. If Mathlib adds these declarations, delete
them here.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasInitial C] [HasBinaryCoproducts C]
  {D : Type u₂} [Category.{v₂} D] [HasInitial D] [HasBinaryCoproducts D]

attribute [local instance] monoidalOfHasFiniteCoproducts symmetricOfHasFiniteCoproducts

namespace LaxMonoidal

/-- Any functor between categories with finite coproducts is lax monoidal for the cocartesian
monoidal structures, with unit `initialComparison F` and tensorator `coprodComparison F`.

This is not made an instance because it would create a diamond for the lax monoidal structure on
the identity and composition of functors. -/
@[instance_reducible]
noncomputable def ofHasFiniteCoproducts (F : C ⥤ D) : F.LaxMonoidal where
  ε := initialComparison F
  μ X Y := coprodComparison F X Y
  μ_natural_left f X := by
    refine coprod.hom_ext ?_ ?_ <;> simp [-Functor.map_comp, ← Functor.map_comp]
  μ_natural_right X g := by
    refine coprod.hom_ext ?_ ?_ <;> simp [-Functor.map_comp, ← Functor.map_comp]
  associativity X Y Z := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) ?_ <;>
      simp [-Functor.map_comp, ← Functor.map_comp, monoidalOfHasFiniteCoproducts.associator_hom]
  left_unitality X := by
    refine coprod.hom_ext (initial.hom_ext _ _) ?_
    simp [-Functor.map_comp, ← Functor.map_comp, monoidalOfHasFiniteCoproducts.leftUnitor_hom,
      coprod.inr_desc]
  right_unitality X := by
    refine coprod.hom_ext ?_ (initial.hom_ext _ _)
    simp [-Functor.map_comp, ← Functor.map_comp, monoidalOfHasFiniteCoproducts.rightUnitor_hom,
      coprod.inl_desc]

variable (F : C ⥤ D)

@[simp]
lemma ofHasFiniteCoproducts_ε :
    letI := ofHasFiniteCoproducts F
    ε F = initialComparison F := rfl

@[simp]
lemma ofHasFiniteCoproducts_μ (X Y : C) :
    letI := ofHasFiniteCoproducts F
    μ F X Y = coprodComparison F X Y := rfl

end LaxMonoidal

namespace Monoidal

open LaxMonoidal OplaxMonoidal

variable (F : C ⥤ D) [PreservesFiniteCoproducts F]

/-- A functor preserving finite coproducts is monoidal for the cocartesian monoidal structures:
the comparison maps of `Functor.LaxMonoidal.ofHasFiniteCoproducts` are isomorphisms.

This is not made an instance because it would create a diamond for the monoidal structure on the
identity and composition of functors. -/
@[instance_reducible]
noncomputable def ofHasFiniteCoproducts : F.Monoidal :=
  letI := LaxMonoidal.ofHasFiniteCoproducts F
  have : IsIso (ε F) := inferInstanceAs (IsIso (initialComparison F))
  have (X Y : C) : IsIso (μ F X Y) := inferInstanceAs (IsIso (coprodComparison F X Y))
  .ofLaxMonoidal F

@[simp]
lemma ofHasFiniteCoproducts_ε :
    letI := ofHasFiniteCoproducts F
    ε F = initialComparison F := rfl

@[simp]
lemma ofHasFiniteCoproducts_μ (X Y : C) :
    letI := ofHasFiniteCoproducts F
    μ F X Y = coprodComparison F X Y := rfl

@[simp]
lemma ofHasFiniteCoproducts_η :
    letI := ofHasFiniteCoproducts F
    η F = CategoryTheory.inv (initialComparison F) := rfl

@[simp]
lemma ofHasFiniteCoproducts_δ (X Y : C) :
    letI := ofHasFiniteCoproducts F
    δ F X Y = CategoryTheory.inv (coprodComparison F X Y) := rfl

end Monoidal

namespace Braided

/-- A functor preserving finite coproducts is braided for the cocartesian symmetric monoidal
structures.

This is not made an instance because it would create a diamond for the monoidal structure on the
identity and composition of functors. -/
@[instance_reducible]
noncomputable def ofHasFiniteCoproducts (F : C ⥤ D) [PreservesFiniteCoproducts F] :
    F.Braided :=
  letI := Monoidal.ofHasFiniteCoproducts F
  { braided := fun X Y => by
      refine coprod.hom_ext ?_ ?_ <;>
        simp [-Functor.map_comp, ← Functor.map_comp] }

end Braided

end CategoryTheory.Functor
