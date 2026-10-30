module

public import Mathlib.Data.Fintype.Card

/-!
# Refinements of interfaces over fixed positions

An *interface* in bundle form is a type of directions `E` with a map `π : E → Q` to a type of
positions (questions), so the answers to question `q` are the fiber `π⁻¹(q)`. This is the
polynomial `Σ_{q : Q} y^{π⁻¹(q)}`, presented as a map `E → Q`.

A *refinement* `p₀ → p₁` keeps the positions and gives a backward map `g : E₁ → E₀` over `Q`:
each new answer says which old answer it refines. It is *preserving* on a set `U` of positions
(those declared unchanged) when every old answer is still reachable (`g` surjective) and `g` is
injective over `U`, so over `U` nothing changes up to renaming.

A *profile* `s : α → Q → E` gives each agent's answer to each question; refinements are required
to keep earlier answers (`Commit`).

## Main definitions

* `LeanTo.Interface.IsOver π₀ π₁ g`: `g` maps answers over `q` to answers over `q`.
* `LeanTo.Interface.CartOn π₁ U g`: `g` is injective on answers over positions in `U`.
* `LeanTo.Interface.Preserving π₀ π₁ U g`: `IsOver`, surjective, and `CartOn U`.
* `LeanTo.Interface.ProfWF π s`: each agent answers each question with an answer over it.
* `LeanTo.Interface.Commit g s₀ s₁`: the new profile refines the old one.

## Main results

* `LeanTo.Interface.Preserving.comp`: preserving refinements compose, with unchanged set the
  intersection `U ∩ V`.
* `LeanTo.Interface.Commit.comp`: commitments compose.
-/

@[expose] public section

namespace LeanTo

namespace Interface

universe u v w x y

variable {Q : Type u} {E₀ : Type v} {E₁ : Type w} {E₂ : Type x}

/-- `g` lies over the positions: it sends each new answer to an old answer to the same question. -/
def IsOver (π₀ : E₀ → Q) (π₁ : E₁ → Q) (g : E₁ → E₀) : Prop := ∀ e, π₀ (g e) = π₁ e

/-- `g` is injective on new answers to questions in `U` (cartesian over `U`). -/
def CartOn (π₁ : E₁ → Q) (U : Q → Bool) (g : E₁ → E₀) : Prop :=
  ∀ e e', U (π₁ e) = true → g e = g e' → e = e'

/-- A refinement that lies over the positions, keeps every old answer reachable, and is exact
(injective) over the positions in `U`. -/
def Preserving (π₀ : E₀ → Q) (π₁ : E₁ → Q) (U : Q → Bool) (g : E₁ → E₀) : Prop :=
  IsOver π₀ π₁ g ∧ Function.Surjective g ∧ CartOn π₁ U g

section Decidable

variable [Fintype E₀] [Fintype E₁] [DecidableEq E₀] [DecidableEq E₁] [DecidableEq Q]

instance (π₀ : E₀ → Q) (π₁ : E₁ → Q) (g : E₁ → E₀) : Decidable (IsOver π₀ π₁ g) :=
  inferInstanceAs (Decidable (∀ e, π₀ (g e) = π₁ e))

instance (π₁ : E₁ → Q) (U : Q → Bool) (g : E₁ → E₀) : Decidable (CartOn π₁ U g) :=
  inferInstanceAs (Decidable (∀ e e', U (π₁ e) = true → g e = g e' → e = e'))

instance (π₀ : E₀ → Q) (π₁ : E₁ → Q) (U : Q → Bool) (g : E₁ → E₀) :
    Decidable (Preserving π₀ π₁ U g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

/-- Refinements over the positions compose. -/
theorem IsOver.comp {π₀ : E₀ → Q} {π₁ : E₁ → Q} {π₂ : E₂ → Q} {g₁ : E₁ → E₀} {g₂ : E₂ → E₁}
    (h₁ : IsOver π₀ π₁ g₁) (h₂ : IsOver π₁ π₂ g₂) : IsOver π₀ π₂ (g₁ ∘ g₂) :=
  fun e ↦ (h₁ (g₂ e)).trans (h₂ e)

/-- Exactness composes on the intersection of the unchanged sets. -/
theorem CartOn.comp {π₁ : E₁ → Q} {π₂ : E₂ → Q} {U V : Q → Bool} {g₁ : E₁ → E₀}
    {g₂ : E₂ → E₁} (h₂o : IsOver π₁ π₂ g₂) (h₁ : CartOn π₁ U g₁) (h₂ : CartOn π₂ V g₂) :
    CartOn π₂ (fun q ↦ U q && V q) (g₁ ∘ g₂) := by
  intro e e' hU heq
  rw [Bool.and_eq_true] at hU
  exact h₂ e e' hU.2 (h₁ _ _ (by rw [h₂o]; exact hU.1) heq)

/-- Preserving refinements compose: the composite is preserving on the positions both declared
unchanged. -/
theorem Preserving.comp {π₀ : E₀ → Q} {π₁ : E₁ → Q} {π₂ : E₂ → Q} {U V : Q → Bool}
    {g₁ : E₁ → E₀} {g₂ : E₂ → E₁} (h₁ : Preserving π₀ π₁ U g₁) (h₂ : Preserving π₁ π₂ V g₂) :
    Preserving π₀ π₂ (fun q ↦ U q && V q) (g₁ ∘ g₂) :=
  ⟨h₁.1.comp h₂.1, h₁.2.1.comp h₂.2.1, CartOn.comp h₂.1 h₁.2.2 h₂.2.2⟩

section Profile

variable {α : Type y}

/-- A well-formed profile: each agent answers each question `q` with an answer over `q`. -/
def ProfWF (π : E₀ → Q) (s : α → Q → E₀) : Prop := ∀ a q, π (s a q) = q

/-- The new profile `s₁` refines the old profile `s₀` along `g`: no earlier answer is rewritten. -/
def Commit (g : E₁ → E₀) (s₀ : α → Q → E₀) (s₁ : α → Q → E₁) : Prop :=
  ∀ a q, g (s₁ a q) = s₀ a q

instance [Fintype α] [Fintype Q] [DecidableEq Q] (π : E₀ → Q) (s : α → Q → E₀) :
    Decidable (ProfWF π s) :=
  inferInstanceAs (Decidable (∀ a q, π (s a q) = q))

instance [Fintype α] [Fintype Q] [DecidableEq E₀] (g : E₁ → E₀) (s₀ : α → Q → E₀)
    (s₁ : α → Q → E₁) : Decidable (Commit g s₀ s₁) :=
  inferInstanceAs (Decidable (∀ a q, g (s₁ a q) = s₀ a q))

/-- Commitments compose. -/
theorem Commit.comp {g₁ : E₁ → E₀} {g₂ : E₂ → E₁} {s₀ : α → Q → E₀} {s₁ : α → Q → E₁}
    {s₂ : α → Q → E₂} (h₁ : Commit g₁ s₀ s₁) (h₂ : Commit g₂ s₁ s₂) : Commit (g₁ ∘ g₂) s₀ s₂ :=
  fun a q ↦ (congrArg g₁ (h₂ a q)).trans (h₁ a q)

end Profile

end Interface

end LeanTo
