module

import LeanTo

open scoped SetRel

/-! ### Left substitution (companion side) -/

/-- `Nat.succ`'s graph followed by `≤` relates `2` to `5`, because `3 ≤ 5`. -/
example : 2 ~[Nat.succ.graph ○ {p : ℕ × ℕ | p.1 ≤ p.2}] 5 := by
  rw [SetRel.mem_graph_comp]
  decide

/-- ...and does not relate `5` to `5`, because `6 ≤ 5` fails. -/
example : ¬ 5 ~[Nat.succ.graph ○ {p : ℕ × ℕ | p.1 ≤ p.2}] 5 := by
  rw [SetRel.mem_graph_comp]
  decide

example {α β γ : Type*} (f : α → β) (R : SetRel β γ) :
    f.graph ○ R = {p | (f p.1, p.2) ∈ R} :=
  SetRel.graph_comp_eq_preimage f R

/-! ### Right substitution (conjoint side) -/

/-- `≤` followed by the converse of `Nat.succ`'s graph relates `a` to `c` iff `a ≤ c + 1`. -/
example : 4 ~[{p : ℕ × ℕ | p.1 ≤ p.2} ○ Nat.succ.graph.inv] 3 := by
  rw [SetRel.mem_comp_inv_graph]
  decide

example : ¬ 5 ~[{p : ℕ × ℕ | p.1 ≤ p.2} ○ Nat.succ.graph.inv] 3 := by
  rw [SetRel.mem_comp_inv_graph]
  decide

example {α β γ : Type*} (R : SetRel α β) (g : γ → β) :
    R ○ g.graph.inv = {p | (p.1, g p.2) ∈ R} :=
  SetRel.comp_inv_graph_eq_preimage R g

/-! ### The Prop-valued form is existing Mathlib

`Relation.Comp` (local notation `∘r`) uses the same diagrammatic order. Graph substitution there
is `Relation.fun_eq_comp` (left) and `Relation.comp_eq_fun` (right). These are Mathlib's, not
contributions of this package. -/

/-- A function's graph as a Prop-valued relation, composed on the left: substitution, by
`Relation.fun_eq_comp`. -/
example {α β γ : Type*} (f : α → β) (r : β → γ → Prop) (a : α) (c : γ) :
    Relation.Comp (fun x y => f x = y) r a c ↔ r (f a) c := by
  rw [Relation.fun_eq_comp]

/-- On the right Mathlib composes with the converse graph `(· = g ·)`. -/
example {α β γ : Type*} (r : α → β → Prop) (g : γ → β) (a : α) (c : γ) :
    Relation.Comp r (fun y z => y = g z) a c ↔ r a (g c) := by
  rw [Relation.comp_eq_fun]

/-- The two representations agree definitionally: `SetRel.comp` is `Relation.Comp` on
membership. -/
example {α β γ : Type*} (R : SetRel α β) (S : SetRel β γ) (a : α) (c : γ) :
    a ~[R ○ S] c ↔ Relation.Comp (· ~[R] ·) (· ~[S] ·) a c :=
  Iff.rfl

/-- `Function.graph f` is the `SetRel` form of the Prop-valued graph `(f · = ·)`. -/
example {α β : Type*} (f : α → β) (a : α) (b : β) : a ~[f.graph] b ↔ f a = b :=
  Function.mem_graph

/-! ### Restriction along two graphs

The relational instance of Shulman's composite `₍f₎B ⊙ M ⊙ D₍g₎ : A ⇸ C` (his `⊙` is also
diagrammatic): the companion `f.graph`, then `M`, then the conjoint `g.graph.inv`. -/

/-- Restricting `≤` along `(· * 2)` and `(· + 1)`: `a` is related to `c` iff `2 * a ≤ c + 1`. -/
example : 2 ~[(· * 2 : ℕ → ℕ).graph ○ {p : ℕ × ℕ | p.1 ≤ p.2} ○ (· + 1 : ℕ → ℕ).graph.inv] 3 := by
  rw [SetRel.graph_comp_comp_inv_graph]
  exact (by decide : 2 * 2 ≤ 3 + 1)

example : ¬ 3 ~[(· * 2 : ℕ → ℕ).graph ○ {p : ℕ × ℕ | p.1 ≤ p.2} ○ (· + 1 : ℕ → ℕ).graph.inv] 3 := by
  rw [SetRel.graph_comp_comp_inv_graph]
  exact (by decide : ¬ 3 * 2 ≤ 3 + 1)

/-- On the Prop-valued side the same restriction is Mathlib's `Function.bicompl`, via
`Relation.fun_eq_comp` and `Relation.comp_eq_fun`. -/
example {α β γ δ : Type*} (f : α → β) (m : β → δ → Prop) (g : γ → δ) :
    Relation.Comp (Relation.Comp (f · = ·) m) (· = g ·) = Function.bicompl m f g := by
  rw [Relation.fun_eq_comp, Relation.comp_eq_fun]
  rfl

/-- The `SetRel` restriction is `Function.bicompl` on membership. -/
example {α β γ δ : Type*} (f : α → β) (M : SetRel β δ) (g : γ → δ) (a : α) (c : γ) :
    a ~[f.graph ○ M ○ g.graph.inv] c ↔ Function.bicompl (· ~[M] ·) f g a c := by
  rw [SetRel.graph_comp_comp_inv_graph]
  rfl

/-! ### The graph is left adjoint to its converse

In the ordered category of relations (diagrammatic order), `f.graph ⊣ f.graph.inv`: -/

/-- Unit: two points with the same image under `f` are related by `f.graph ○ f.graph.inv`; in
particular every point is related to itself. -/
example {α β : Type*} (f : α → β) : (SetRel.id : SetRel α α) ⊆ f.graph ○ f.graph.inv :=
  SetRel.id_subset_graph_comp_inv_graph f

/-- The unit is strict for a non-injective map: `2` and `3` have the same `· / 2`. -/
example : 2 ~[(· / 2 : ℕ → ℕ).graph ○ (· / 2 : ℕ → ℕ).graph.inv] 3 ∧
    ¬ 2 ~[(SetRel.id : SetRel ℕ ℕ)] 3 := by
  rw [SetRel.mem_comp_inv_graph, Function.mem_graph, SetRel.mem_id]
  decide

/-- Counit: `f.graph.inv ○ f.graph` relates only equal points. -/
example {α β : Type*} (f : α → β) : f.graph.inv ○ f.graph ⊆ (SetRel.id : SetRel β β) :=
  SetRel.inv_graph_comp_graph_subset_id f

/-- The counit is strict for a non-surjective map: nothing reaches `0` under `Nat.succ`. -/
example : 0 ~[(SetRel.id : SetRel ℕ ℕ)] 0 ∧ ¬ 0 ~[Nat.succ.graph.inv ○ Nat.succ.graph] 0 := by
  simp

/-! ### Why this is not a double-category result

Read relations as a double category: objects are types, vertical arrows are functions, horizontal
arrows are relations, and a cell from `N : SetRel α γ` to `M : SetRel β δ` with vertical
boundaries `f : α → β` and `g : γ → δ` is the inclusion `N ⊆ Prod.map f g ⁻¹' M`. Cells are
propositions, so the category is thin. Restriction's universal property, factoring a cell with
boundaries `(f ∘ h, g ∘ k)` uniquely through the restriction of `M` along `(f, g)`, is then
definitional, and uniqueness is proof irrelevance. Nothing below bears on Shulman's Theorem 4.1
for pseudo double categories, where cells carry data and equations (4.3)–(4.4) are real. -/

example {α β γ δ α' γ' : Type*} (f : α → β) (g : γ → δ) (h : α' → α) (k : γ' → γ)
    (M : SetRel β δ) (N : SetRel α' γ') :
    N ⊆ Prod.map (f ∘ h) (g ∘ k) ⁻¹' M ↔ N ⊆ Prod.map h k ⁻¹' (Prod.map f g ⁻¹' M) :=
  Iff.rfl

/-! ### Axioms -/

/-- info: 'SetRel.graph_comp_eq_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SetRel.graph_comp_eq_preimage

/-- info: 'SetRel.mem_graph_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SetRel.mem_graph_comp

/-- info: 'SetRel.comp_inv_graph_eq_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SetRel.comp_inv_graph_eq_preimage

/-- info: 'SetRel.mem_comp_inv_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SetRel.mem_comp_inv_graph

/-- info: 'SetRel.graph_comp_comp_inv_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SetRel.graph_comp_comp_inv_graph

/-- info: 'SetRel.id_subset_graph_comp_inv_graph' does not depend on any axioms -/
#guard_msgs in #print axioms SetRel.id_subset_graph_comp_inv_graph

/-- info: 'SetRel.inv_graph_comp_graph_subset_id' does not depend on any axioms -/
#guard_msgs in #print axioms SetRel.inv_graph_comp_graph_subset_id
