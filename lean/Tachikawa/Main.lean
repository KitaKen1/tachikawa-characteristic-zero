import Tachikawa.Statement
import TachikawaCharZero.ArtinWitness

/-!
# Negative answer to the rational symmetric Tachikawa assertion

The public theorem has exactly the FC-style statement and name. Its proof
specializes the universal assertion to the actual rational witnesses.
-/

namespace TachikawaCharZero
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- Tachikawa's second conjecture restricted to finite-dimensional symmetric
rational algebras: does vanishing of all positive self-Ext groups force a finite
module to be projective? The answer is negative [Ki26]. The scalar-tower
hypothesis makes the rational module structure compatible with the algebra action.
The answer applies to the whole universal assertion, not to a fixed pair. -/
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
  constructor
  · exact False.elim
  · intro h
    let : Module.Finite ℚ TriangularWitness.Gamma := TriangularWitness.Gamma_finite
    let : Module.Finite ℚ TriangularWitness.M := TriangularWitness.M_finite
    have hs : SymmetricOver ℚ TriangularWitness.Gamma :=
      TriangularWitness.Gamma_symmetric
    exact TriangularNonprojective.M_nonprojective
      (h TriangularWitness.Gamma hs TriangularWitness.M ArtinWitness.self_ext_vanishing)

#print axioms tachikawaSecondConjecture

end
end TachikawaCharZero
