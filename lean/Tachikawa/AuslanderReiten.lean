import Tachikawa.Main

/-!
# Negative answer to the general Artin-algebra Auslander--Reiten assertion

The independently stated conjecture has the pinned FC ambient hypotheses.
The rational witness also has vanishing positive Ext into the regular module.
-/

namespace TachikawaCharZero

/-- The general Artin-algebra Auslander--Reiten conjecture: does a finite
module with all positive Ext groups into itself and the regular module equal
to zero have to be projective? The answer is negative. The rational symmetric
counterexample [Ki26] satisfies both premises; self-injectivity gives the
regular-module Ext vanishing. No commutativity of the algebra is assumed. -/
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
  change False ↔ FCStatement.ArtinAuslanderReiten
  exact ⟨False.elim, ArtinWitness.not_artinAuslanderReiten⟩

#print axioms artinAuslanderReiten

end TachikawaCharZero
