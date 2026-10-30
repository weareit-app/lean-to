module

public import LeanTo.RelationAlgebra.Expr
public import Mathlib.Logic.Equiv.Sum

/-!
# Automorphism invariance of relation-algebra expressions

Every operation of `LeanTo.RelExpr` commutes with relabeling the carrier by a permutation. So if a
permutation preserves every atom, it preserves every expression. This gives a nondefinability
test that works for the full language, including complement, converse and closure: a relation
that some atom-preserving permutation moves is not the value of any expression. (Homomorphism
invariance, the usual test for positive-existential fragments, does not cover complement.)

The same argument shows that some queries have no correct answer in the language. A query asks,
for a fixed `asker`, for a nonempty set of answers all of which are `Good`. A permutation that
preserves the atoms, fixes the asker and moves every good answer to a bad one is an
*obstruction*: no expression meets the query.

## Main definitions

* `LeanTo.RelExpr.GoalMet R asker Good`: `R` relates `asker` to something, and only to `Good`
  elements.
* `LeanTo.RelExpr.Obstruction I asker Good`: an atom-preserving permutation that fixes `asker` and
  sends every good element to a bad one.

## Main results

* `LeanTo.RelExpr.isInvariant_eval`: atom-preserving permutations preserve every expression.
* `LeanTo.RelExpr.eval_ne_of_not_isInvariant`: a relation moved by an atom-preserving permutation
  is not definable.
* `LeanTo.RelExpr.Obstruction.not_goalMet`: an obstruction rules out every expression.
* `LeanTo.RelExpr.Obstruction.not_isInvariant_of_goalMet_sumElim`: if adding one atom `R` makes
  the query reachable, the obstruction's permutation does not preserve `R`.
-/

@[expose] public section

namespace LeanTo

universe u v

namespace RelExpr

variable {α : Type u} {A : Type v}

open BoolRel

/-- If a permutation preserves every atom, it preserves the relation every expression denotes. -/
theorem isInvariant_eval [DecidableEq α] [Fintype α] (I : A → BoolRel α) {σ : Equiv.Perm α}
    (hI : ∀ a, IsInvariant σ (I a)) : ∀ e : RelExpr A, IsInvariant σ (eval I e)
  | atom a => hI a
  | idE => isInvariant_idRel σ
  | emptyE => fun _ _ ↦ rfl
  | comp e f => isInvariant_comp (isInvariant_eval I hI e) (isInvariant_eval I hI f)
  | union e f => fun x y ↦ by
    simp only [eval, isInvariant_eval I hI e x y, isInvariant_eval I hI f x y]
  | inter e f => fun x y ↦ by
    simp only [eval, isInvariant_eval I hI e x y, isInvariant_eval I hI f x y]
  | compl e => fun x y ↦ by simp only [eval, isInvariant_eval I hI e x y]
  | conv e => fun x y ↦ isInvariant_eval I hI e y x
  | star e => isInvariant_closure (isInvariant_eval I hI e)

/-- Nondefinability by invariance: if a permutation preserves every atom but not `R`, then no
expression denotes `R`. -/
theorem eval_ne_of_not_isInvariant [DecidableEq α] [Fintype α] (I : A → BoolRel α)
    {σ : Equiv.Perm α} (hI : ∀ a, IsInvariant σ (I a)) {R : BoolRel α}
    (hR : ¬IsInvariant σ R) (e : RelExpr A) : eval I e ≠ R := by
  rintro rfl
  exact hR (isInvariant_eval I hI e)

/-- The relation `R` meets the query of `asker` for `Good` answers: it relates `asker` to at least
one element, and every element it relates `asker` to is `Good`. -/
def GoalMet (R : BoolRel α) (asker : α) (Good : α → Bool) : Prop :=
  (∃ y, R asker y = true) ∧ ∀ y, R asker y = true → Good y = true

instance [Fintype α] (R : BoolRel α) (asker : α) (Good : α → Bool) :
    Decidable (GoalMet R asker Good) :=
  inferInstanceAs (Decidable ((∃ y, R asker y = true) ∧ ∀ y, R asker y = true → Good y = true))

/-- An obstruction to meeting the query of `asker` for `Good` answers with atoms `I`: a permutation
that preserves every atom, fixes `asker`, and sends every good element to one that is not good. -/
structure Obstruction (I : A → BoolRel α) (asker : α) (Good : α → Bool) where
  /-- The witnessing permutation. -/
  σ : Equiv.Perm α
  /-- `σ` preserves every atom. -/
  atomsInv : ∀ a, IsInvariant σ (I a)
  /-- `σ` fixes the asker. -/
  fixes : σ asker = asker
  /-- `σ` sends every good element to one that is not good. -/
  breaks : ∀ y, Good y = true → Good (σ y) = false

namespace Obstruction

variable [DecidableEq α] [Fintype α] {I : A → BoolRel α} {asker : α} {Good : α → Bool}

/-- Obstruction soundness: if an obstruction exists, no expression meets the query. -/
theorem not_goalMet (ob : Obstruction I asker Good) (e : RelExpr A) :
    ¬GoalMet (eval I e) asker Good := by
  rintro ⟨⟨y, hy⟩, hgood⟩
  have hσy : eval I e asker (ob.σ y) = true := by
    have := isInvariant_eval I ob.atomsInv e asker y
    rwa [ob.fixes, hy] at this
  have := ob.breaks y (hgood y hy)
  rw [hgood _ hσy] at this
  exact Bool.noConfusion this

/-- A repair must break the obstruction: if adding one atom `R` to `I` gives an expression that
meets the query, then the obstruction's permutation does not preserve `R`. -/
theorem not_isInvariant_of_goalMet_sumElim (ob : Obstruction I asker Good) (R : BoolRel α)
    (e : RelExpr (A ⊕ Unit)) (h : GoalMet (eval (Sum.elim I fun _ ↦ R) e) asker Good) :
    ¬IsInvariant ob.σ R := fun hR ↦
  not_goalMet (I := Sum.elim I fun _ ↦ R)
    ⟨ob.σ, fun | .inl a => ob.atomsInv a | .inr _ => hR, ob.fixes, ob.breaks⟩ e h

end Obstruction

end RelExpr

end LeanTo
