import Mathlib

/-!
# Shared definitions for the rational Tachikawa and Artin targets

The definition of `SymmetricOver` matches FClikelean/TachikawaCharZero.lean.
The identity macro has the same propositional meaning as FC's `answer(False)`.
This Mathlib-only proof project does not import an unproved FC declaration.
-/

macro "answer(" t:term ")" : term => pure t

namespace TachikawaCharZero

/-- A $K$-algebra isomorphic to its dual as an $A$-bimodule. -/
def SymmetricOver (K A : Type) [Field K] [Ring A]
    [Algebra K A] : Prop :=
  ∃ e : A ≃ₗ[K] Module.Dual K A,
    (∀ a b c : A, e (a * b) c = e b (c * a)) ∧
    (∀ a b c : A, e (a * b) c = e a (b * c))

end TachikawaCharZero
