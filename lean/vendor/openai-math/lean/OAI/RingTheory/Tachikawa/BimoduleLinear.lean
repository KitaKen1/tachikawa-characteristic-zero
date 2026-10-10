import OAI.RingTheory.Tachikawa.Twisting

/-! Characteristic-independent excerpt from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Only imports and outer wrappers are replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def homOfLinear {M N : ModuleCat.{0} (Alg k R S)} (f : M →ₗ[k] N)
    (hf : ∀ (r : R) (s : Sᵐᵒᵖ) (x : M), f ((r ⊗ₜ[k] s) • x) = (r ⊗ₜ[k] s) • f x) :
    M ⟶ N := ModuleCat.ofHom (X := M) (Y := N)
  { toFun := f
    map_add' := f.map_add
    map_smul' a x := by
      induction a using TensorProduct.inductionOn with
      | add a b ha hb => simp only [add_smul,map_add,ha,hb]
      | tmul r s => exact hf r s x }

end Tachikawa.Enveloping



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def resUnderlyingEquiv (φ : R →ₐ[k] S) (M : ModuleCat.{0} S) :
    (res φ).obj M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) • (show M from x) = c • (show M from x)
    rw [φ.commutes]
    rfl

instance resFinite (φ : R →ₐ[k] S) (M : ModuleCat.{0} S) [FiniteDimensional k M] :
    FiniteDimensional k ((res φ).obj M) :=
  Module.Finite.equiv (resUnderlyingEquiv φ M).symm

end Tachikawa.AlgebraInduction

end
end OAI
