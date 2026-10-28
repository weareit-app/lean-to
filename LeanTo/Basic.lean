module

public import Mathlib.Order.Basic

/-!
# Skeleton check

Proves that this package builds against the pinned Mathlib. It is not a library
contribution; replace it once real definitions land.
-/

namespace LeanTo

/-- Every element of a preorder is below itself. -/
public theorem skeleton_le_refl {α : Type*} [Preorder α] (a : α) : a ≤ a :=
  le_refl a

end LeanTo
