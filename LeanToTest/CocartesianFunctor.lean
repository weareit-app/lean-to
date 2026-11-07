module

public import LeanTo.CategoryTheory.Monoidal.CocartesianFunctor
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Tests for `LeanTo.CategoryTheory.Monoidal.CocartesianFunctor`

The lax structure on an arbitrary functor, the monoidal and braided structures on a functor
preserving finite coproducts, and the identity functor on types.
-/

open CategoryTheory Limits MonoidalCategory Functor LaxMonoidal OplaxMonoidal

attribute [local instance] monoidalOfHasFiniteCoproducts symmetricOfHasFiniteCoproducts

variable {C D : Type*} [Category* C] [HasInitial C] [HasBinaryCoproducts C]
  [Category* D] [HasInitial D] [HasBinaryCoproducts D]

section Lax

variable (F : C ⥤ D) (X Y : C)

attribute [local instance] LaxMonoidal.ofHasFiniteCoproducts

/-- The unit of the lax structure is the initial comparison map. -/
example : ε F = initialComparison F := by simp

/-- The tensorator is the coproduct comparison map, so it is the identity on each summand. -/
example : coprod.inl ≫ μ F X Y = F.map coprod.inl := by simp

example : coprod.inr ≫ μ F X Y = F.map coprod.inr := by simp

end Lax

section Strong

variable (F : C ⥤ D) [PreservesFiniteCoproducts F] (X Y : C)

attribute [local instance] Monoidal.ofHasFiniteCoproducts

example : ε F = initialComparison F := by simp

example : coprod.inl ≫ μ F X Y = F.map coprod.inl := by simp

/-- `η` and `δ` are the inverses of the comparison maps. -/
example : η F = inv (initialComparison F) := by simp

example : δ F X Y = inv (coprodComparison F X Y) := by simp

example : μ F X Y ≫ δ F X Y = 𝟙 _ := by simp

/-- The braided structure. -/
noncomputable example : F.Braided := Braided.ofHasFiniteCoproducts F

attribute [local instance] Braided.ofHasFiniteCoproducts in
example : μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X :=
  Braided.braided X Y

end Strong

section Types

/-- For the identity functor on types the tensorator is the identity. -/
example (X Y : Type) :
    letI := LaxMonoidal.ofHasFiniteCoproducts (𝟭 Type)
    μ (𝟭 Type) X Y = 𝟙 (X ⨿ Y) := by
  refine coprod.hom_ext ?_ ?_ <;> simp [coprodComparison]

noncomputable example : (𝟭 Type).Braided := Braided.ofHasFiniteCoproducts (𝟭 Type)

end Types
