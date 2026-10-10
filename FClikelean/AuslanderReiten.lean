/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import FormalConjecturesUtil

/-!
# The Auslander-Reiten conjecture

The Artin-algebra conjecture asks whether a finite module is projective
when its positive Ext groups into itself and the regular module vanish [AR75].

References:
- [AR75] M. Auslander and I. Reiten,
  *On a generalized version of the Nakayama conjecture*,
  Proc. Amer. Math. Soc. 52 (1975), 69-74.
  https://doi.org/10.1090/S0002-9939-1975-0389977-6
- [Ki26] K. Kitamura, *A characteristic-zero Tachikawa counterexample* (2026).
  Lean proof: lean/Tachikawa/AuslanderReiten.lean.
-/

@[expose] public section

namespace TachikawaCharZero

/-- The Auslander-Reiten conjecture for Artin algebras [AR75].
The answer is no [Ki26]. -/
@[category research solved, AMS 16,
    formal_proof using lean4 at "https://github.com/KitaKen1/tachikawa-characteristic-zero/blob/main/lean/Tachikawa/AuslanderReiten.lean#L17"]
theorem artinAuslanderReiten :
    answer(False) ↔
      ∀ (Λ : Type) [Ring Λ] (M : Type) [AddCommGroup M] [Module Λ M]
        [Module.Finite Λ M] (A : Type) [CommRing A] [IsArtinianRing A]
        [Algebra A Λ] [Module.Finite A Λ],
        (∀ n : ℕ, 0 < n →
          Subsingleton (CategoryTheory.Abelian.Ext
            (ModuleCat.of Λ M) (ModuleCat.of Λ Λ) n)) →
        (∀ n : ℕ, 0 < n →
          Subsingleton (CategoryTheory.Abelian.Ext
            (ModuleCat.of Λ M) (ModuleCat.of Λ M) n)) →
          Module.Projective Λ M := by
  sorry

end TachikawaCharZero
