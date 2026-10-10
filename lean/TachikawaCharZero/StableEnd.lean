import TachikawaCharZero.TensorProfile
import TachikawaCharZero.SingleScalarEnd

/-! The actual stable endomorphism space of X. The ideal of maps through
finite projectives is zero: any nonzero scalar endomorphism would make
the identity factor through a projective, contradicting nonprojectivity. -/
namespace TachikawaCharZero.StableEnd
noncomputable section
open CategoryTheory TensorProfile OAI.Tachikawa
open scoped ModuleCat.Algebra

instance finiteE : Module.Finite E X₂ :=
  Module.Finite.of_restrictScalars_finite ℚ E X₂

def scalarMap : ℚ →ₗ[ℚ] (X₂ →ₗ[E] X₂) where
  toFun c := c • LinearMap.id
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := by simp only [smul_eq_mul, RingHom.id_apply, smul_smul]

theorem scalarMap_bijective : Function.Bijective scalarMap := by
  constructor
  · intro c d h
    have hh := congrArg (fun f : X₂ →ₗ[E] X₂ =>
      groundEquiv (f (groundEquiv.symm 1))) h
    simpa only [scalarMap, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one] using hh
  · intro f
    obtain ⟨c,hc⟩ := SingleScalarEnd.module_one ℚ E X₂ finrank_one (ModuleCat.ofHom f)
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro x
    exact congrArg (fun g : X₂ ⟶ X₂ => g x) hc.symm

def scalarEquiv : ℚ ≃ₗ[ℚ] (X₂ →ₗ[E] X₂) := LinearEquiv.ofBijective scalarMap scalarMap_bijective

theorem projectiveFactors_eq_bot :
    projectiveFactors (k := ℚ) (R := E) (M := X₂) (N := X₂)=⊥ := by
  apply eq_bot_iff.mpr
  change ∀ f ∈ projectiveFactors (k := ℚ) (R := E) (M := X₂) (N := X₂), f ∈ (⊥ : Submodule ℚ _)
  intro f hf
  obtain ⟨c,rfl⟩ := scalarMap_bijective.2 f
  by_cases hc : c=0
  · simp [hc,scalarMap]
  · have hscalar : c⁻¹ • scalarMap c = LinearMap.id := by
      simp only [scalarMap, LinearMap.coe_mk, AddHom.coe_mk, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
    have hid : LinearMap.id (R := E) (M := X₂) ∈ projectiveFactors (k := ℚ) := by
      rw [← hscalar]
      exact Submodule.smul_mem _ c⁻¹ hf
    exact False.elim (not_projective (id_mem_projectiveFactors_iff.mp hid))

def equiv : StableHom (k := ℚ) (R := E) (M := X₂) (N := X₂) ≃ₗ[ℚ] ℚ :=
  ((projectiveFactors (k := ℚ) (R := E) (M := X₂) (N := X₂)).quotEquivOfEqBot
    projectiveFactors_eq_bot).trans scalarEquiv.symm

theorem finrank_one : Module.finrank ℚ
    (StableHom (k := ℚ) (R := E) (M := X₂) (N := X₂))=1 := by
  rw [equiv.finrank_eq]
  exact Module.finrank_self ℚ

theorem identity_coordinate : equiv (stableClass (k := ℚ) (LinearMap.id (R := E)))=1 := by
  change scalarEquiv.symm
    ((projectiveFactors (k := ℚ) (R := E) (M := X₂) (N := X₂)).quotEquivOfEqBot
      projectiveFactors_eq_bot (Submodule.Quotient.mk LinearMap.id))=1
  rw [Submodule.quotEquivOfEqBot_apply_mk]
  apply scalarEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change LinearMap.id = scalarMap 1
  simp [scalarMap]

end
end TachikawaCharZero.StableEnd
