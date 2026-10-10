/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import FormalConjecturesUtil

/-!
# Tachikawa's second conjecture in characteristic zero

The rational symmetric case asks whether vanishing positive self-Ext
forces finite-dimensional modules to be projective [Tac73, Section 8].

References:
- [Tac73] H. Tachikawa, *Quasi-Frobenius Rings and Generalizations*,
  Lecture Notes in Mathematics 351 (1973), Section 8.
  https://link.springer.com/chapter/10.1007/BFb0060005
- [Ki26] K. Kitamura, *A characteristic-zero Tachikawa counterexample* (2026).
  Lean proof: lean/Tachikawa/Main.lean.
-/

@[expose] public section

namespace TachikawaCharZero

/-- A $K$-algebra isomorphic to its dual as an $A$-bimodule. -/
def SymmetricOver (K A : Type) [Field K] [Ring A]
    [Algebra K A] : Prop :=
  ∃ e : A ≃ₗ[K] Module.Dual K A,
    (∀ a b c : A, e (a * b) c = e b (c * a)) ∧
    (∀ a b c : A, e (a * b) c = e a (b * c))

/-- The rational symmetric case of Tachikawa's second conjecture [Tac73, Section 8].
The answer is no [Ki26]. -/
@[category research solved, AMS 16,
    formal_proof using lean4 at "https://github.com/KitaKen1/tachikawa-characteristic-zero/blob/main/lean/Tachikawa/Main.lean#L21"]
theorem tachikawaSecondConjecture :
    answer(False) ↔
      ∀ (Γ : Type) [Ring Γ] [Algebra ℚ Γ] [Module.Finite ℚ Γ],
        SymmetricOver ℚ Γ →
          ∀ (M : Type) [AddCommGroup M] [Module Γ M] [Module ℚ M]
            [IsScalarTower ℚ Γ M] [Module.Finite ℚ M],
            (∀ n : ℕ, 0 < n →
              Subsingleton (CategoryTheory.Abelian.Ext
                (ModuleCat.of Γ M) (ModuleCat.of Γ M) n)) →
              Module.Projective Γ M := by
  sorry

end TachikawaCharZero
