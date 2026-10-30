module

public import LeanTo.Interface.Refinement
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Merging two independent refinements

Two refinements `gA : A → E₀` and `gB : B → E₀` of the same interface merge into the fiber
product `{(a, b) | gA a = gB b}` over `E₀`. Refinements point backward (new answers to old ones),
so in the category of interfaces and refinements this pullback of answer types is a pushout of
interfaces. With the positions fixed, it is computed fiber by fiber.

The exactness claims of the two refinements do not both survive in general. The merged
refinement is exact over a set of positions exactly when both refinements are
(`cartOn_mergeMap_iff`). So a refinement's claim that some positions are unchanged survives a
merge only on positions the other refinement also leaves unchanged.

## Main definitions

* `LeanTo.Interface.Merge gA gB`: the fiber product of `gA` and `gB`.
* `LeanTo.Interface.mergeMap gA gB`: the merged refinement `Merge gA gB → E₀`.

## Main results

* `LeanTo.Interface.pullback_universal`: the fiberwise universal property of the fiber product,
  for families of answer types indexed by positions.
* `LeanTo.Interface.cartOn_mergeMap_iff`: the merge is exact over `U` iff both refinements are.
* `LeanTo.Interface.isPushout_op_of_isPullback_left`: a square of interfaces whose answer types
  form a pullback in `Type` is a pushout in the category of interfaces and refinements,
  `(Over Q)ᵒᵖ`.
-/

@[expose] public section

namespace LeanTo

namespace Interface

universe u v w x y

/-- The fiberwise universal property of the fiber product: compatible maps from `C i` into
`A i` and `B i` factor uniquely through `{(a, b) | gA i a = gB i b}`, for every position `i`. -/
theorem pullback_universal {P : Type u} {A B E₀ C : P → Type v} (gA : ∀ i, A i → E₀ i)
    (gB : ∀ i, B i → E₀ i) (uA : ∀ i, C i → A i) (uB : ∀ i, C i → B i)
    (h : ∀ i c, gA i (uA i c) = gB i (uB i c)) :
    ∃ u : ∀ i, C i → {x : A i × B i // gA i x.1 = gB i x.2},
      (∀ i c, (u i c).1.1 = uA i c ∧ (u i c).1.2 = uB i c) ∧
      ∀ u' : ∀ i, C i → {x : A i × B i // gA i x.1 = gB i x.2},
        (∀ i c, (u' i c).1.1 = uA i c ∧ (u' i c).1.2 = uB i c) → u' = u :=
  ⟨fun i c ↦ ⟨(uA i c, uB i c), h i c⟩, fun _ _ ↦ ⟨rfl, rfl⟩, fun _ hu' ↦
    funext fun i ↦ funext fun c ↦ Subtype.ext (Prod.ext (hu' i c).1 (hu' i c).2)⟩

variable {Q : Type u} {E₀ : Type v} {A : Type w} {B : Type x}

/-- The merge of two refinements `gA` and `gB` of the same interface: pairs of answers that refine
the same old answer. -/
def Merge (gA : A → E₀) (gB : B → E₀) : Type (max w x) := {p : A × B // gA p.1 = gB p.2}

/-- The merged refinement, sending a compatible pair to the old answer both refine. -/
def mergeMap (gA : A → E₀) (gB : B → E₀) (m : Merge gA gB) : E₀ := gA m.1.1

/-- The merge is exact over `U` if and only if both refinements are. Only the forward direction
uses surjectivity. -/
theorem cartOn_mergeMap_iff {π₀ : E₀ → Q} {πA : A → Q} {πB : B → Q} {gA : A → E₀}
    {gB : B → E₀} (hA : IsOver π₀ πA gA) (hB : IsOver π₀ πB gB) (sA : Function.Surjective gA)
    (sB : Function.Surjective gB) (U : Q → Bool) :
    CartOn (π₀ ∘ mergeMap gA gB) U (mergeMap gA gB) ↔ CartOn πA U gA ∧ CartOn πB U gB := by
  constructor
  · intro h
    refine ⟨fun a a' hU he ↦ ?_, fun b b' hU he ↦ ?_⟩
    · obtain ⟨b, hb⟩ := sB (gA a)
      have := h ⟨(a, b), hb.symm⟩ ⟨(a', b), by rw [← he, hb]⟩
        (by simp only [Function.comp, mergeMap]; rw [hA]; exact hU) he
      exact congrArg (fun m : Merge gA gB ↦ m.1.1) this
    · obtain ⟨a, ha⟩ := sA (gB b)
      have := h ⟨(a, b), ha⟩ ⟨(a, b'), by rw [ha, he]⟩
        (by simp only [Function.comp, mergeMap]; rw [ha, hB]; exact hU) rfl
      exact congrArg (fun m : Merge gA gB ↦ m.1.2) this
  · rintro ⟨hA', hB'⟩ ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ hU he
    simp only [Function.comp, mergeMap] at hU he
    have haa : a = a' := hA' a a' (by rwa [← hA]) he
    have hbb : b = b' := hB' b b' (by rwa [← hB, ← hab]) (by rw [← hab, ← hab', he])
    subst haa hbb
    rfl

open CategoryTheory Limits

/-- A commuting square of interfaces over `Q` whose underlying square of answer types is a
pullback in `Type` is a pullback in `Over Q`, so a pushout in the category of interfaces and
refinements `(Over Q)ᵒᵖ`. -/
theorem isPushout_op_of_isPullback_left {W X Y Z : Over Q} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst.left snd.left f.left g.left) :
    IsPushout g.op f.op snd.op fst.op :=
  (IsPullback.of_map_of_faithful (Over.forget Q) h).op

end Interface

end LeanTo
