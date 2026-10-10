import TachikawaCharZero.RightDualDimension
import TachikawaCharZero.Simple
import OAI.RingTheory.Tachikawa.Symmetry

/-! The actual rational symmetric starting algebras T=C⋉DC and E=T⊗T.
The tensor symmetrizing-form argument is adapted from OpenAI Math's
Tachikawa/Tensor.lean, fixed at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0). The already compiled generic trivial-extension API is reused;
none of the characteristic-two final construction is asserted here. -/
namespace TachikawaCharZero.SymmetricTensor
noncomputable section
open scoped TensorProduct
open OAI.Tachikawa
variable {k R S : Type*} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))

def trace : R ⊗[k] S →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp (TensorProduct.map t.linear u.linear)

theorem trace_tmul (r : R) (s : S) : trace t u (r ⊗ₜ[k] s)=t.linear r*u.linear s := rfl

theorem trace_comm (a b : R ⊗[k] S) : trace t u (a*b)=trace t u (b*a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r s =>
    induction b using TensorProduct.inductionOn with
    | tmul r' s' => simp only [Algebra.TensorProduct.tmul_mul_tmul,trace_tmul,
        t.comm r r',u.comm s s']
    | add b c hb hc => simp only [mul_add,add_mul,map_add,hb,hc]
  | add a c ha hc => simp only [add_mul,mul_add,map_add,ha,hc]

variable [FiniteDimensional k R] [FiniteDimensional k S]

def dualEquiv : R ⊗[k] S ≃ₗ[k] Module.Dual k (R ⊗[k] S) :=
  (TensorProduct.congr (t.dualEquiv.restrictScalars k) (u.dualEquiv.restrictScalars k)).trans
    (TensorProduct.dualDistribEquiv k R S)

theorem dualEquiv_apply (a b : R ⊗[k] S) : dualEquiv t u a b=trace t u (b*a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r s =>
    induction b using TensorProduct.inductionOn with
    | tmul r' s' =>
      dsimp only [dualEquiv,DualBimodule]
      simp only [Algebra.TensorProduct.tmul_mul_tmul,trace_tmul]
      change u.linear (s'*s)*t.linear (r'*r)=t.linear (r'*r)*u.linear (s'*s)
      exact mul_comm _ _
    | add b c hb hc => simp only [map_add,add_mul,hb,hc]
  | add a c ha hc => simp only [map_add,LinearMap.add_apply,mul_add,ha,hc]

def form : SymmetrizingForm (k := k) (R := R ⊗[k] S) where
  linear := trace t u
  comm := trace_comm t u
  nondegenerate a h := by
    apply (dualEquiv t u).injective
    apply LinearMap.ext
    intro b
    rw [dualEquiv_apply,trace_comm,h]
    simp

end
end TachikawaCharZero.SymmetricTensor

namespace TachikawaCharZero.Starting
noncomputable section
open Resolution
open OAI.Tachikawa
open scoped TensorProduct

abbrev T := TrivialExtension ℚ A
abbrev B := A ⊗[ℚ] A
abbrev E := T ⊗[ℚ] T

def dualBimoduleIso : Dual ≃ₗ[A] DualBimodule ℚ A where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dualBimoduleIso_right (a : Aᵐᵒᵖ) (φ : Dual) :
    dualBimoduleIso (a • φ)=a • dualBimoduleIso φ := rfl

theorem T_finrank : Module.finrank ℚ T=20 := by
  change Module.finrank ℚ (A × Module.Dual ℚ A)=20
  rw [Module.finrank_prod,Subspace.dual_finrank_eq,
    OAI.ArExplicit.BaseAlgebra.finrank_eq_ten]

theorem B_finrank : Module.finrank ℚ B=100 := by
  rw [Module.finrank_tensorProduct,OAI.ArExplicit.BaseAlgebra.finrank_eq_ten]

theorem E_finrank : Module.finrank ℚ E=400 := by
  rw [Module.finrank_tensorProduct,T_finrank]

def T_form : SymmetrizingForm (k := ℚ) (R := T) := TrivialExtension.symmetrizingForm
def E_form : SymmetrizingForm (k := ℚ) (R := E) := SymmetricTensor.form T_form T_form

theorem T_symmetric : SymmetricOver ℚ T := T_form.symmetricOver
theorem E_symmetric : SymmetricOver ℚ E := E_form.symmetricOver
theorem T_injective : Module.Injective T T := T_form.injective
theorem E_injective : Module.Injective E E := E_form.injective

def T_character : T →ₐ[ℚ] ℚ := character.comp (TrivSqZeroExt.fstHom ℚ A (DualBimodule ℚ A))

theorem T_character_inl (a : A) : T_character (TrivSqZeroExt.inl a)=character a := rfl
theorem T_character_inr (φ : DualBimodule ℚ A) : T_character (TrivSqZeroExt.inr φ)=0 := rfl

end
end TachikawaCharZero.Starting
