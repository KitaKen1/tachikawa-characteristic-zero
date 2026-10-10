import TachikawaCharZero.SignedSourceComparison
import OAI.RingTheory.Tachikawa.InductionLeftComparison

/-! Forgetting a right enveloping twist leaves the left action unchanged
and restricts the right action along the same algebra automorphism.
The comparisons are actual natural isomorphisms with underlying identity. -/
namespace TachikawaCharZero.TwistSideRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev twist (σ : R ≃ₐ[k] R) :=
  AlgebraInduction.res
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) σ.op).toAlgHom
abbrev rightRestriction (σ : R ≃ₐ[k] R) := AlgebraInduction.res σ.op.toAlgHom

def leftObjIso (σ : R ≃ₐ[k] R) (M : ModuleCat (Enveloping.Alg k R R)) :
    (Enveloping.leftFunctor (k := k)).obj ((twist σ).obj M) ≅
      (Enveloping.leftFunctor (k := k)).obj M :=
  (AddEquiv.toLinearEquiv (R := R)
    (M := ↑((Enveloping.leftFunctor (k := k)).obj ((twist σ).obj M)))
    (M₂ := ↑((Enveloping.leftFunctor (k := k)).obj M))
    (by rfl) (by
      intro r x
      change (r ⊗ₜ[k] σ.op (1 : Rᵐᵒᵖ)) • (show M from x) =
        (r ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (show M from x)
      rw [map_one])).toModuleIso

def leftComparison (σ : R ≃ₐ[k] R) :
    twist σ ⋙ Enveloping.leftFunctor (k := k) ≅ Enveloping.leftFunctor (k := k) :=
  NatIso.ofComponents (leftObjIso σ) (by intro M N f; ext x; rfl)

def rightObjIso (σ : R ≃ₐ[k] R) (M : ModuleCat (Enveloping.Alg k R R)) :
    (Enveloping.rightFunctor (k := k)).obj ((twist σ).obj M) ≅
      (rightRestriction σ).obj ((Enveloping.rightFunctor (k := k)).obj M) :=
  (AddEquiv.toLinearEquiv (R := Rᵐᵒᵖ)
    (M := ↑((Enveloping.rightFunctor (k := k)).obj ((twist σ).obj M)))
    (M₂ := ↑((rightRestriction σ).obj ((Enveloping.rightFunctor (k := k)).obj M)))
    (by rfl) (by intro r x; rfl)).toModuleIso

def rightComparison (σ : R ≃ₐ[k] R) :
    twist σ ⋙ Enveloping.rightFunctor (k := k) ≅
      Enveloping.rightFunctor (k := k) ⋙ rightRestriction σ :=
  NatIso.ofComponents (rightObjIso σ) (by intro M N f; ext x; rfl)

instance rightRestriction_projective (σ : R ≃ₐ[k] R) :
    (rightRestriction σ).PreservesProjectiveObjects := by
  change (ModuleCat.restrictScalars σ.op.toRingEquiv.toRingHom).PreservesProjectiveObjects
  infer_instance

end
end TachikawaCharZero.TwistSideRestriction
