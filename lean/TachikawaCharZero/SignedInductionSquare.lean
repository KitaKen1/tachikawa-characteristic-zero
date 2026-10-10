import TachikawaCharZero.SignedTrivialAutomorphism
import TachikawaCharZero.InducedTwistedSocle

/-! The actual right-twist automorphisms of B^e and E^e commute with
inclusion. This supplies the algebra square for a future comparison
of signed induction with untwisted induction. No comparison of complexes
or source high-degree exactness is asserted here. -/
namespace TachikawaCharZero.SignedInductionSquare
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OAI.Tachikawa
open scoped TensorProduct

section Generic
variable {k A R : Type} [Field k] [Ring A] [Ring R] [Algebra k A] [Algebra k R]

theorem right_tensor_square (φ : A →ₐ[k] R) (θ : A ≃ₐ[k] A) (ψ : R ≃ₐ[k] R)
    (h : ∀ a, ψ (φ a) = φ (θ a)) :
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) ψ.op).toAlgHom.comp
        (Algebra.TensorProduct.map φ φ.op) =
      (Algebra.TensorProduct.map φ φ.op).comp
        (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) θ.op).toAlgHom := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change φ a ⊗ₜ[k] MulOpposite.op (ψ (φ b.unop)) =
      φ a ⊗ₜ[k] MulOpposite.op (φ (θ b.unop))
    rw [h]
  | add a b ha hb => simp only [map_add,ha,hb]
end Generic

open ScalingSocle
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def rightTwistB : BE ≃ₐ[ℚ] BE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ScalingSocle.B ≃ₐ[ℚ] ScalingSocle.B) TwistedFactorization.theta.op

def rightTwistE : EE ≃ₐ[ℚ] EE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[ℚ] E) SignedTrivialAutomorphism.signedE.op

theorem inclusion_square : rightTwistE.toAlgHom.comp inclusionBE =
    inclusionBE.comp rightTwistB.toAlgHom :=
  right_tensor_square inclusionB TwistedFactorization.theta SignedTrivialAutomorphism.signedE
    SignedTrivialAutomorphism.signedE_inclusion

end
end TachikawaCharZero.SignedInductionSquare
