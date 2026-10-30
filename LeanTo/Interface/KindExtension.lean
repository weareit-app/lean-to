module

public import Mathlib.Logic.Function.Basic

/-!
# Extensions that add positions

A refinement over fixed positions can split answers but cannot add a question. An *extension*
`p₀ → p₁` may add positions: it embeds the old positions into the new ones by an injective map
`f`, and over each old position `q` it identifies the new answers to `f q` with the old answers to
`q` by a bijection (it is cartesian on every old position). New positions outside the image of
`f` are unconstrained. This is the shape of growing a registry of kinds.

Nothing else in the library depends on this file.

## Main definitions

* `LeanTo.Interface.KindExtension π₀ π₁`: an extension from `π₀ : E₀ → Q₀` to `π₁ : E₁ → Q₁`.

## Main results

* `LeanTo.Interface.KindExtension.comp`: extensions compose.
-/

@[expose] public section

namespace LeanTo

namespace Interface

universe u₀ u₁ u₂ v₀ v₁ v₂

/-- An extension of the interface `π₀ : E₀ → Q₀` to `π₁ : E₁ → Q₁` that may add positions: an
injective map on positions and, over each old position, a bijection between the new answers and
the old ones (a lens that is cartesian on every old position). -/
structure KindExtension {Q₀ : Type u₀} {E₀ : Type v₀} {Q₁ : Type u₁} {E₁ : Type v₁}
    (π₀ : E₀ → Q₀) (π₁ : E₁ → Q₁) where
  /-- Where each old position goes. -/
  onPos : Q₀ → Q₁
  /-- No two old positions are identified. -/
  onPos_injective : Function.Injective onPos
  /-- Each new answer to an old position names an old answer to it. -/
  onDir : ∀ q, {e : E₁ // π₁ e = onPos q} → {d : E₀ // π₀ d = q}
  /-- Over each old position the answers correspond exactly. -/
  onDir_bijective : ∀ q, Function.Bijective (onDir q)

namespace KindExtension

variable {Q₀ : Type u₀} {E₀ : Type v₀} {Q₁ : Type u₁} {E₁ : Type v₁} {Q₂ : Type u₂}
  {E₂ : Type v₂} {π₀ : E₀ → Q₀} {π₁ : E₁ → Q₁} {π₂ : E₂ → Q₂}

/-- The composite of two extensions is an extension. -/
def comp (k₁ : KindExtension π₀ π₁) (k₂ : KindExtension π₁ π₂) : KindExtension π₀ π₂ where
  onPos := k₂.onPos ∘ k₁.onPos
  onPos_injective := k₂.onPos_injective.comp k₁.onPos_injective
  onDir q e := k₁.onDir q (k₂.onDir (k₁.onPos q) e)
  onDir_bijective q := (k₁.onDir_bijective q).comp (k₂.onDir_bijective (k₁.onPos q))

/-- The identity extension. -/
def id (π₀ : E₀ → Q₀) : KindExtension π₀ π₀ where
  onPos := _root_.id
  onPos_injective := Function.injective_id
  onDir _ e := e
  onDir_bijective _ := Function.bijective_id

end KindExtension

end Interface

end LeanTo
