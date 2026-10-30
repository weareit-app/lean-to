module

public import LeanTo.RelationAlgebra.BoolRel

/-!
# Relation-algebra expressions with closure

The syntax of relation-algebra expressions over a set of atoms, with reflexive–transitive closure,
and their evaluation as Boolean relations on a finite carrier. Complement and converse make the
language closed under first-order definability without parameters on the operations it has; for
example relational division `R ÷ S` is `compl (comp (compl R) (conv S))`.

## Main definitions

* `LeanTo.RelExpr A`: expressions over atoms `A`.
* `LeanTo.RelExpr.eval I e`: the relation `e` denotes when each atom `a` denotes `I a`.
-/

@[expose] public section

namespace LeanTo

universe u v

/-- Relation-algebra expressions over atoms `A`: atoms, identity, the empty relation, composition,
union, intersection, complement, converse and reflexive–transitive closure. -/
inductive RelExpr (A : Type v) where
  /-- An atomic relation. -/
  | atom (a : A)
  /-- The identity relation. -/
  | idE
  /-- The empty relation. -/
  | emptyE
  /-- Relational composition. -/
  | comp (e f : RelExpr A)
  /-- Union. -/
  | union (e f : RelExpr A)
  /-- Intersection. -/
  | inter (e f : RelExpr A)
  /-- Complement. -/
  | compl (e : RelExpr A)
  /-- Converse. -/
  | conv (e : RelExpr A)
  /-- Reflexive–transitive closure. -/
  | star (e : RelExpr A)
  deriving DecidableEq, Repr

namespace RelExpr

variable {α : Type u} {A : Type v}

/-- The relation an expression denotes on the finite carrier `α`, when each atom `a` denotes
`I a`. -/
def eval [DecidableEq α] [Fintype α] (I : A → BoolRel α) : RelExpr A → BoolRel α
  | atom a => I a
  | idE => BoolRel.idRel
  | emptyE => fun _ _ ↦ false
  | comp e f => BoolRel.comp (eval I e) (eval I f)
  | union e f => fun x y ↦ eval I e x y || eval I f x y
  | inter e f => fun x y ↦ eval I e x y && eval I f x y
  | compl e => fun x y ↦ !eval I e x y
  | conv e => fun x y ↦ eval I e y x
  | star e => BoolRel.closure (eval I e)

end RelExpr

end LeanTo
