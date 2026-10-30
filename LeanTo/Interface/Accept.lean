module

public import LeanTo.Interface.Translation
public import LeanTo.RelationAlgebra.Invariance

/-!
# Accepting a proposed refinement

A proposal to extend an interface is a new answer type with its positions, a refinement map, the
positions it declares unchanged, a new profile, and a query (plan) for a goal. `Accept` holds
exactly when the refinement is preserving, the new profile is well formed and keeps every earlier
answer, and the plan meets the goal in the extended language. Every clause is decidable on finite
data, so a concrete proposal is checked by `decide`.

## Main definitions

* `LeanTo.Interface.Accept`: the acceptance predicate for a proposed refinement and plan.
-/

@[expose] public section

namespace LeanTo

namespace Interface

universe u v w x y

variable {α : Type u} {B : Type v} {Q : Type x} {E₀ : Type w} {E₁ : Type y}

/-- Accept a proposed refinement `g : E₁ → E₀` with unchanged positions `U`, new profile `s₁` and
plan `plan` for the query of `asker` for `Good` answers: the refinement is preserving, the profile
is well formed and keeps the old answers `s₀`, and the plan meets the goal. -/
def Accept [DecidableEq α] [Fintype α] [DecidableEq E₁] (base : B → BoolRel α) (π₀ : E₀ → Q)
    (s₀ : α → Q → E₀) (π₁ : E₁ → Q) (g : E₁ → E₀) (U : Q → Bool) (s₁ : α → Q → E₁)
    (plan : RelExpr (TestAtom B E₁)) (asker : α) (Good : α → Bool) : Prop :=
  Preserving π₀ π₁ U g ∧ ProfWF π₁ s₁ ∧ Commit g s₀ s₁ ∧
    RelExpr.GoalMet (RelExpr.eval (interp base π₁ s₁) plan) asker Good

instance [DecidableEq α] [Fintype α] [DecidableEq E₀] [DecidableEq E₁] [Fintype E₀] [Fintype E₁]
    [DecidableEq Q] [Fintype Q] (base : B → BoolRel α) (π₀ : E₀ → Q) (s₀ : α → Q → E₀)
    (π₁ : E₁ → Q) (g : E₁ → E₀) (U : Q → Bool) (s₁ : α → Q → E₁)
    (plan : RelExpr (TestAtom B E₁)) (asker : α) (Good : α → Bool) :
    Decidable (Accept base π₀ s₀ π₁ g U s₁ plan asker Good) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Interface

end LeanTo
