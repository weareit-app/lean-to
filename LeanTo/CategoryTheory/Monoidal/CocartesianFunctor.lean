module

public import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Functors preserving finite coproducts are braided monoidal

Give categories with an initial object and binary coproducts the cocartesian monoidal structure
`(⨿, ⊥_)`: Mathlib's `monoidalOfHasFiniteCoproducts` and `symmetricOfHasFiniteCoproducts`. A
functor that preserves binary coproducts and the initial object is then braided monoidal, with
unit isomorphism `PreservesInitial.iso F` and tensorator the comparison isomorphism
`PreservesColimitPair.iso F X Y : F X ⨿ F Y ≅ F (X ⨿ Y)`.

This is the cocartesian counterpart of Mathlib's `Functor.Monoidal.ofChosenFiniteProducts` and
`Functor.Braided.ofChosenFiniteProducts`, which do the same for finite products and
`CartesianMonoidalCategory`. Mathlib has no cocartesian monoidal class, so the structure here is the
one Mathlib puts on a category with finite coproducts as a local instance.

## Main definitions

* `LeanTo.coreMonoidalOfPreservesCoproducts F : F.CoreMonoidal`
* `LeanTo.monoidalOfPreservesCoproducts F : F.Monoidal`
* `LeanTo.braidedOfPreservesCoproducts F : F.Braided`
-/

@[expose] public section

namespace LeanTo

open CategoryTheory Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasInitial C] [HasBinaryCoproducts C]
  {D : Type u₂} [Category.{v₂} D] [HasInitial D] [HasBinaryCoproducts D]
  (F : C ⥤ D) [PreservesColimitsOfShape (Discrete WalkingPair) F]
  [PreservesColimitsOfShape (Discrete PEmpty.{1}) F]

attribute [local instance] monoidalOfHasFiniteCoproducts symmetricOfHasFiniteCoproducts

instance : PreservesColimit (Functor.empty.{0} C) F := by
  have := preservesColimitsOfShape_of_equiv
    (Discrete.equivalence (Equiv.equivOfIsEmpty PEmpty.{1} PEmpty.{1})) F
  infer_instance

/-- The comparison isomorphisms make a coproduct-preserving functor monoidal for the cocartesian
monoidal structures. -/
noncomputable def coreMonoidalOfPreservesCoproducts : F.CoreMonoidal where
  εIso := (PreservesInitial.iso F).symm
  μIso X Y := PreservesColimitPair.iso F X Y
  μIso_hom_natural_left f X' := by
    refine coprod.hom_ext ?_ ?_ <;>
      simp [PreservesColimitPair.iso_hom, -Functor.map_comp, ← Functor.map_comp]
  μIso_hom_natural_right X' f := by
    refine coprod.hom_ext ?_ ?_ <;>
      simp [PreservesColimitPair.iso_hom, -Functor.map_comp, ← Functor.map_comp]
  associativity X Y Z := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) ?_ <;>
      simp [PreservesColimitPair.iso_hom, -Functor.map_comp, ← Functor.map_comp,
        monoidalOfHasFiniteCoproducts.associator_hom]
  left_unitality X := by
    refine coprod.hom_ext ?_ ?_
    · exact initial.hom_ext _ _
    · simp [PreservesColimitPair.iso_hom, -Functor.map_comp, ← Functor.map_comp,
        monoidalOfHasFiniteCoproducts.leftUnitor_hom, coprod.inr_desc]
  right_unitality X := by
    refine coprod.hom_ext ?_ ?_
    · simp [PreservesColimitPair.iso_hom, -Functor.map_comp, ← Functor.map_comp,
        monoidalOfHasFiniteCoproducts.rightUnitor_hom, coprod.inl_desc]
    · exact initial.hom_ext _ _

/-- The tensorator is the coproduct comparison isomorphism. -/
theorem coreMonoidalOfPreservesCoproducts_μIso (X Y : C) :
    (coreMonoidalOfPreservesCoproducts F).μIso X Y = PreservesColimitPair.iso F X Y := rfl

/-- The unit isomorphism is the initial-object comparison isomorphism. -/
theorem coreMonoidalOfPreservesCoproducts_εIso :
    (coreMonoidalOfPreservesCoproducts F).εIso = (PreservesInitial.iso F).symm := rfl

/-- A coproduct-preserving functor is monoidal for the cocartesian monoidal structures. -/
@[instance_reducible] noncomputable def monoidalOfPreservesCoproducts : F.Monoidal :=
  (coreMonoidalOfPreservesCoproducts F).toMonoidal

/-- **A coproduct-preserving functor is braided monoidal** for the cocartesian symmetric monoidal
structures. -/
@[instance_reducible] noncomputable def braidedOfPreservesCoproducts : F.Braided :=
  letI := monoidalOfPreservesCoproducts F
  { braided := fun X Y => by
      change ((coreMonoidalOfPreservesCoproducts F).μIso X Y).hom ≫ _ = _ ≫
        ((coreMonoidalOfPreservesCoproducts F).μIso Y X).hom
      refine coprod.hom_ext ?_ ?_ <;>
        simp [coreMonoidalOfPreservesCoproducts, PreservesColimitPair.iso_hom,
          -Functor.map_comp, ← Functor.map_comp] }

end LeanTo
