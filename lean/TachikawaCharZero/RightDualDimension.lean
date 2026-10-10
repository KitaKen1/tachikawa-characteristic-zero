import TachikawaCharZero.Opposite
import TachikawaCharZero.LeftDualResolution
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! The right-side finite projective dimension is transported from the
checked left resolution using the explicit anti-involution. -/
namespace TachikawaCharZero.Resolution
noncomputable section
open CategoryTheory
attribute [local instance] RingHomInvPair.of_ringEquiv

def reverseLinear : A →ₗ[ℚ] A where
  toFun := reverse
  map_add' := reverse_add
  map_smul' := reverse_smul

def dualReverse (φ : Dual) : Dual := φ.comp reverseLinear

def dualOppositeIso : (ModuleCat.of A Dual) ≃ₛₗ[
    RingHomClass.toRingHom oppositeIso.toRingEquiv] (ModuleCat.of Aᵐᵒᵖ Dual) where
  toFun := dualReverse
  invFun := dualReverse
  left_inv φ := by
    apply dual_ext
    intro x
    change φ (reverse (reverse x))=φ x
    rw [reverse_reverse]
  right_inv φ := by
    apply dual_ext
    intro x
    change φ (reverse (reverse x))=φ x
    rw [reverse_reverse]
  map_add' φ ψ := by apply dual_ext; intro x; rfl
  map_smul' a φ := by
    apply dual_ext
    intro x
    change φ (reverse x*a)=φ (reverse (reverse a*x))
    rw [reverse_mul,reverse_reverse]

theorem rightDual_projectiveDimension :
    HasProjectiveDimensionLE (ModuleCat.of Aᵐᵒᵖ Dual) 2 := by
  have := leftDual_projectiveDimension
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv
    oppositeIso.toRingEquiv dualOppositeIso 2

end
end TachikawaCharZero.Resolution
