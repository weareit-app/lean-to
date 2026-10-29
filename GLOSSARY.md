# Glossary

**Graph** (of a function `f : α → β`): the relation `{(a, b) | f a = b}`, Mathlib's `Function.graph f : SetRel α β`.

**Composition** (of relations): diagrammatic. `R ○ S` relates `a` to `c` when some `b` has `a ~[R] b` and `b ~[S] c`; first `R`, then `S`. Not function composition `∘`, which is applicative.

**Converse**: a relation with its arguments swapped, `SetRel.inv`. _Avoid_: inverse, unless it is one.

**Restriction** (of `M : SetRel β δ` along `f : α → β` and `g : γ → δ`): the relation `{(a, c) | (f a, g c) ∈ M}`. Equal to `f.graph ○ M ○ g.graph.inv`.

**Companion**, **conjoint**: in a double category, horizontal arrows `₍f₎B : A ⇸ B` and `B₍f₎ : B ⇸ A` with binding cells (Shulman, *Framed Bicategories and Monoidal Fibrations*). In relations they are the graph and its converse. This repository has not formalized the double-category notion; for relations it uses the words only for the graph and converse.
