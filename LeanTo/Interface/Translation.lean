module

public import LeanTo.RelationAlgebra.Expr
public import LeanTo.Interface.Refinement
public import Mathlib.Data.FinEnum

/-!
# Queries over an interface, and their translation along a refinement

Relation-algebra queries over agents whose atoms are fixed base relations (such as who knows whom)
and *tests* `test d`, which hold at `(a, a)` when agent `a` gives answer `d`. Along a refinement
`g : E₁ → E₀`, an old test `test d` translates to the union of the new tests `test e` with
`g e = d`. With a well-formed new profile that keeps every old answer (`Commit`), every old query
keeps its exact meaning.

## Main definitions

* `LeanTo.Interface.TestAtom B E`: base atoms `B` and tests on answers `E`.
* `LeanTo.Interface.interp base π s`: the relation each atom denotes under profile `s`.
* `LeanTo.Interface.translate g e`: translate a query along `g`.

## Main results

* `LeanTo.Interface.eval_translate`: translation preserves meaning.
-/

@[expose] public section

namespace LeanTo

namespace Interface

universe u v w x y

/-- Atoms of a query language over an interface with answers `E`: fixed base relations from `B`,
and a test for each answer. -/
inductive TestAtom (B : Type v) (E : Type w) where
  /-- A fixed base relation between agents. -/
  | base (b : B)
  /-- The test `{(a, a) | agent a gives answer d}`. -/
  | test (d : E)
  deriving DecidableEq, Repr

variable {α : Type u} {B : Type v} {Q : Type x} {E₀ : Type w} {E₁ : Type y}

/-- Atoms are base atoms or answers. -/
def TestAtom.equivSum : TestAtom B E₀ ≃ B ⊕ E₀ where
  toFun
    | .base b => .inl b
    | .test d => .inr d
  invFun
    | .inl b => .base b
    | .inr d => .test d
  left_inv a := by cases a <;> rfl
  right_inv s := by cases s <;> rfl

instance [FinEnum B] [FinEnum E₀] : FinEnum (TestAtom B E₀) :=
  FinEnum.ofEquiv _ TestAtom.equivSum

/-- The relation each atom denotes: base atoms by `base`, and `test d` as the set of `(a, a)` such
that agent `a`'s answer to the question of `d` is `d`. -/
def interp [DecidableEq α] [DecidableEq E₀] (base : B → BoolRel α) (π : E₀ → Q)
    (s : α → Q → E₀) : TestAtom B E₀ → BoolRel α
  | .base b => base b
  | .test d => fun a a' ↦ decide (a = a') && decide (s a (π d) = d)

/-- The union of the tests on the answers in `l`. -/
def unionTests (l : List E₁) : RelExpr (TestAtom B E₁) :=
  l.foldr (fun e acc ↦ .union (.atom (.test e)) acc) .emptyE

/-- Translate a query along a refinement `g`: each old test `test d` becomes the union of the new
tests on the answers that refine `d`; everything else is unchanged. -/
def translate [DecidableEq E₀] [FinEnum E₁] (g : E₁ → E₀) :
    RelExpr (TestAtom B E₀) → RelExpr (TestAtom B E₁)
  | .atom (.base b) => .atom (.base b)
  | .atom (.test d) => unionTests ((FinEnum.toList E₁).filter fun e ↦ g e = d)
  | .idE => .idE
  | .emptyE => .emptyE
  | .comp e f => .comp (translate g e) (translate g f)
  | .union e f => .union (translate g e) (translate g f)
  | .inter e f => .inter (translate g e) (translate g f)
  | .compl e => .compl (translate g e)
  | .conv e => .conv (translate g e)
  | .star e => .star (translate g e)

/-- A union of tests holds at `(a, a')` when `a = a'` and `a` gives one of the answers. -/
theorem eval_unionTests [DecidableEq α] [Fintype α] [DecidableEq E₁] (base : B → BoolRel α)
    (π : E₁ → Q) (s : α → Q → E₁) (l : List E₁) (a a' : α) :
    RelExpr.eval (interp base π s) (unionTests l) a a' =
      decide (∃ e ∈ l, a = a' ∧ s a (π e) = e) := by
  induction l with
  | nil => simp [unionTests, RelExpr.eval]
  | cons e l ih =>
    simp only [unionTests, List.foldr_cons, RelExpr.eval] at ih ⊢
    rw [ih]
    simp [interp, List.mem_cons, or_and_right, exists_or]

/-- Translation preserves meaning: if `g` lies over the positions, the new profile is well formed,
and it keeps every old answer, then every old query means the same after translation. -/
theorem eval_translate [DecidableEq α] [Fintype α] [DecidableEq E₀] [DecidableEq E₁] [FinEnum E₁]
    (base : B → BoolRel α) {π₀ : E₀ → Q} {π₁ : E₁ → Q} {g : E₁ → E₀} {s₀ : α → Q → E₀}
    {s₁ : α → Q → E₁} (hwf : IsOver π₀ π₁ g) (hp : ProfWF π₁ s₁) (hc : Commit g s₀ s₁) :
    ∀ e : RelExpr (TestAtom B E₀),
      RelExpr.eval (interp base π₁ s₁) (translate g e) = RelExpr.eval (interp base π₀ s₀) e
  | .atom (.base b) => rfl
  | .atom (.test d) => by
    funext a a'
    rw [translate, eval_unionTests]
    simp only [RelExpr.eval, interp, List.mem_filter, FinEnum.mem_toList, true_and,
      decide_eq_true_eq]
    by_cases haa : a = a'
    · simp only [haa, true_and, decide_true, Bool.true_and, decide_eq_decide]
      constructor
      · rintro ⟨e, rfl, he⟩
        rw [hwf, ← hc, he]
      · intro hd
        refine ⟨s₁ a' (π₀ d), by rw [hc, hd], ?_⟩
        rw [hp]
    · simp [haa]
  | .idE => rfl
  | .emptyE => rfl
  | .comp e f => by
    simp only [translate, RelExpr.eval, eval_translate base hwf hp hc e,
      eval_translate base hwf hp hc f]
  | .union e f => by
    simp only [translate, RelExpr.eval, eval_translate base hwf hp hc e,
      eval_translate base hwf hp hc f]
  | .inter e f => by
    simp only [translate, RelExpr.eval, eval_translate base hwf hp hc e,
      eval_translate base hwf hp hc f]
  | .compl e => by simp only [translate, RelExpr.eval, eval_translate base hwf hp hc e]
  | .conv e => by simp only [translate, RelExpr.eval, eval_translate base hwf hp hc e]
  | .star e => by simp only [translate, RelExpr.eval, eval_translate base hwf hp hc e]

end Interface

end LeanTo
