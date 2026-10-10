import TachikawaCharZero.LeftDualResolution
import TachikawaCharZero.Simple
import OAI.RingTheory.Tachikawa.CycleQuasiIso

/-! Signed reverse corner complex over Q. The sparse shape follows
OpenAI Math's ReverseResolution.lean at the pinned Apache-2.0 source.
The recurrence uses -2, and the degree-one comparison is -2 rhoX. -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
open OAI.ArExplicit TachikawaCharZero.Resolution
open CategoryTheory CategoryTheory.Limits

def reverseCoeff (n : ℕ) : ℚ := ((-2 : ℚ) ^ (n+2))⁻¹

theorem reverseCoeff_zero : reverseCoeff 0 = 1/4 := by
  norm_num [reverseCoeff]

theorem reverseCoeff_one : reverseCoeff 1 = -1/8 := by
  norm_num [reverseCoeff]

theorem reverseCoeff_step (n : ℕ) : -2 * reverseCoeff (n+1) = reverseCoeff n := by
  unfold reverseCoeff
  rw [show n+1+2=(n+2)+1 by omega, pow_succ]
  field_simp

theorem reverseCoeff_nonexceptional (n : ℕ) :
    1 - 4 * reverseCoeff (n+1) ≠ 0 := by
  have he : 4 * reverseCoeff (n+1) = ((-2:ℚ)^(n+1))⁻¹ := by
    unfold reverseCoeff
    rw [show n+1+2=(n+1)+2 by omega, pow_add]
    norm_num
    field_simp
  rw [he]
  intro h
  have hi : ((-2:ℚ)^(n+1))⁻¹ = 1 := by linarith
  have hp := congrArg (fun z : ℚ => z⁻¹) hi
  simp only [inv_inv, inv_one] at hp
  exact resolution_left_coefficient_ne_zero (n+1) (by omega) (by rw [hp]; norm_num)

theorem ceDiff_consecutive_zero (t : ℚ) (a : Ce) :
    ceDiff t (ceDiff (-2*t) a) = 0 := by
  obtain ⟨a,rfl⟩ := ceIso.surjective a
  rw [ceDiff_iso,ceDiff_iso,consecutive_zero,ceIso.map_zero]

theorem ceDiff_exact_general (t : ℚ) (ht : 1-4*t ≠ 0)
    (ht' : 1-4*(-2*t) ≠ 0) : Function.Exact (ceDiff (-2*t)) (ceDiff t) := by
  intro a
  obtain ⟨a,rfl⟩ := ceIso.surjective a
  constructor
  · intro h
    rw [ceDiff_iso,← ceIso.map_zero] at h
    obtain ⟨b,rfl⟩ := (kernel_iff t ht a).mp (ceIso.injective h)
    refine ⟨ceIso (imagePreimage (-2*t) b), ?_⟩
    rw [ceDiff_iso,rightD_preimage _ ht',next_image_eq_kernel]
  · rintro ⟨b,hb⟩
    rw [← hb]
    exact ceDiff_consecutive_zero t b

theorem reverseD_exact (n : ℕ) :
    Function.Exact (ceDiff (reverseCoeff (n+1))) (ceDiff (reverseCoeff (n+2))) := by
  rw [← reverseCoeff_step (n+1)]
  apply ceDiff_exact_general
  · exact reverseCoeff_nonexceptional (n+1)
  · rw [reverseCoeff_step (n+1)]
    exact reverseCoeff_nonexceptional n

theorem reverseD_comp (n : ℕ) (a : Ce) :
    ceDiff (reverseCoeff (n+1)) (ceDiff (reverseCoeff n) a) = 0 := by
  rw [← reverseCoeff_step n]
  exact ceDiff_consecutive_zero _ a

theorem j_fixed_by_e : BaseAlgebra.basisVector (2:ℚ) .j * vertexE =
    BaseAlgebra.basisVector (2:ℚ) .j := BaseAlgebra.basis_mul 2 .j .e

theorem x_fixed_by_e : BaseAlgebra.basisVector (2:ℚ) .x * vertexE =
    BaseAlgebra.basisVector (2:ℚ) .x := BaseAlgebra.basis_mul 2 .x .e

theorem v_fixed_by_f : BaseAlgebra.basisVector (2:ℚ) .v * vertexF =
    BaseAlgebra.basisVector (2:ℚ) .v := BaseAlgebra.basis_mul 2 .v .f

def rhoJ : Cf →ₗ[A] Ce := Corner.mulRight (BaseAlgebra.basisVector 2 .j) j_fixed_by_e
def rhoX : Ce →ₗ[A] Ce := Corner.mulRight (BaseAlgebra.basisVector 2 .x) x_fixed_by_e
def rhoV : Ce →ₗ[A] Cf := Corner.mulRight (BaseAlgebra.basisVector 2 .v) v_fixed_by_f

theorem rhoJ_iso (a : V₀) : rhoJ (cfIso a) = ceIso ![0,0,0,a 1,0,a 0] := by
  apply Subtype.ext
  change cfEmbed a * BaseAlgebra.basisVector 2 .j = ceEmbed _
  ext i
  cases i <;> simp [cfEmbed,ceEmbed,BaseAlgebra.product]

theorem rhoX_iso (a : V) : rhoX (ceIso a) = ceIso ![0,a 0,0,a 2,0,a 4] := by
  apply Subtype.ext
  change ceEmbed a * BaseAlgebra.basisVector 2 .x = ceEmbed _
  ext i
  cases i <;> simp [ceEmbed,BaseAlgebra.product]

theorem rhoV_iso (a : V) : rhoV (ceIso a) = cfIso ![0,0,a 0,0] := by
  apply Subtype.ext
  change ceEmbed a * BaseAlgebra.basisVector 2 .v = cfEmbed _
  ext i
  cases i <;> simp [cfEmbed,ceEmbed,BaseAlgebra.product]

theorem comparison_one : (ceDiff (reverseCoeff 0)).comp ((-2:ℚ) • rhoX) =
    rhoJ.comp initialMap := by
  apply LinearMap.ext
  intro a
  obtain ⟨a,rfl⟩ := ceIso.surjective a
  rw [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.map_smul_of_tower,
    rhoX_iso,ceDiff_iso,LinearMap.comp_apply,initialMap_iso,rhoJ_iso]
  rw [← ceIso.map_smul]
  apply ceIso.injective.eq_iff.mpr
  ext i
  fin_cases i <;> norm_num [rightD,initialD,reverseCoeff_zero]
  ring

theorem comparison_two : rhoT.comp rhoV = ((-2:ℚ) • rhoX).comp (ceDiff 1) := by
  apply LinearMap.ext
  intro a
  obtain ⟨a,rfl⟩ := ceIso.surjective a
  rw [LinearMap.comp_apply,rhoV_iso,rhoT_iso,LinearMap.comp_apply,
    LinearMap.smul_apply,ceDiff_iso,rhoX_iso,← ceIso.map_smul]
  apply ceIso.injective.eq_iff.mpr
  ext i
  fin_cases i <;> norm_num [rightD]

theorem comparison_bottom : (ceDiff (reverseCoeff 1)).comp rhoJ = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨a,rfl⟩ := cfIso.surjective a
  rw [LinearMap.comp_apply,rhoJ_iso,ceDiff_iso]
  change ceIso _ = 0
  rw [← ceIso.map_zero]
  apply congrArg ceIso
  ext i
  fin_cases i <;> simp [rightD]

theorem comparison_top (c : ℚ) : rhoV.comp (ceDiff c) = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨a,rfl⟩ := ceIso.surjective a
  rw [LinearMap.comp_apply,ceDiff_iso,rhoV_iso]
  change cfIso _ = 0
  rw [← cfIso.map_zero]
  apply congrArg cfIso
  ext i
  fin_cases i <;> simp [rightD]

end
end TachikawaCharZero.ReverseCorner
