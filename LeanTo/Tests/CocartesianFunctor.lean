module

public import LeanTo.CategoryTheory.Monoidal.CocartesianFunctor
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Tests for `LeanTo.CategoryTheory.Monoidal.CocartesianFunctor`

The construction applies to a concrete functor (the identity on types), and its tensorator is the
coproduct comparison isomorphism, which for the identity functor is the identity on `X ⨿ Y`.
-/

open CategoryTheory Limits MonoidalCategory

attribute [local instance] monoidalOfHasFiniteCoproducts symmetricOfHasFiniteCoproducts

/-- The identity functor on types is braided monoidal for `(⨿, ⊥_)`. -/
noncomputable example : (𝟭 (Type 0)).Braided := LeanTo.braidedOfPreservesCoproducts (𝟭 (Type 0))

/-- For the identity functor the tensorator is the identity. -/
example (X Y : Type 0) :
    ((LeanTo.coreMonoidalOfPreservesCoproducts (𝟭 (Type 0))).μIso X Y).hom = 𝟙 (X ⨿ Y) := by
  rw [LeanTo.coreMonoidalOfPreservesCoproducts_μIso]
  exact coprod.hom_ext (by simp [PreservesColimitPair.iso_hom, coprodComparison])
    (by simp [PreservesColimitPair.iso_hom, coprodComparison])
