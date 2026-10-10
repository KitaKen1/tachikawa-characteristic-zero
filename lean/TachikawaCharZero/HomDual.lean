import TachikawaCharZero.DualTwo
import TachikawaCharZero.ProjectivePackaging

/-! Actual Hom-module differentials and their cohomology. Evaluation at
the corner generator connects the checked coordinate complex to Hom(R,C).
The evaluation argument follows the generic API in OpenAI Math's
Tachikawa/Corner.lean, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0). The rational recurrence and its signs are proved here. -/
namespace TachikawaCharZero.Resolution
noncomputable section
open CategoryTheory

abbrev HomE := Ce →ₗ[A] A
abbrev HomF := Cf →ₗ[A] A

def homEEquiv : HomE ≃ₗ[Aᵐᵒᵖ] EC := Corner.homRightEquiv vertexE_idempotent
def homFEquiv : HomF ≃ₗ[Aᵐᵒᵖ] FC := Corner.homRightEquiv vertexF_idempotent

def homDiff (t : ℚ) : HomE →ₗ[Aᵐᵒᵖ] HomE where
  toFun F := F.comp (ceDiff t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homInitial : HomF →ₗ[Aᵐᵒᵖ] HomE where
  toFun F := F.comp initialMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homEEquiv_diff (t : ℚ) (F : HomE) :
    homEEquiv (homDiff t F)=leftDiff t (homEEquiv F) :=
  Corner.homRightEquiv_precomp vertexE_idempotent vertexE_idempotent
    (ell t) (e_fixed_ell t) (ell_mem t) F

theorem homFEquiv_initial (F : HomF) :
    homEEquiv (homInitial F)=leftInitial (homFEquiv F) :=
  Corner.homRightEquiv_precomp vertexE_idempotent vertexF_idempotent
    _ e_fixed_u u_fixed_by_f F

theorem homInitial_injective : Function.Injective homInitial := by
  intro F G h
  apply homFEquiv.injective
  apply leftInitial_injective
  simpa only [homFEquiv_initial] using congrArg homEEquiv h

theorem homInitial_exact : Function.Exact homInitial (homDiff 1) := by
  intro F
  constructor
  · intro h
    have hz : leftDiff 1 (homEEquiv F)=0 := by
      rw [← homEEquiv_diff,h,map_zero]
    obtain ⟨a,ha⟩ := (leftInitial_exact (homEEquiv F)).mp hz
    refine ⟨homFEquiv.symm a,?_⟩
    apply homEEquiv.injective
    rw [homFEquiv_initial,homFEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨G,rfl⟩
    apply homEEquiv.injective
    rw [homEEquiv_diff,homFEquiv_initial,map_zero]
    exact leftInitial_exact.apply_apply_eq_zero _

theorem homDiff_exact_all_degrees (m : ℕ) :
    Function.Exact (homDiff ((-2:ℚ)^(m+1))) (homDiff ((-2:ℚ)^(m+2))) := by
  intro F
  constructor
  · intro h
    have hz : leftDiff ((-2:ℚ)^(m+2)) (homEEquiv F)=0 := by
      rw [← homEEquiv_diff,h,map_zero]
    obtain ⟨a,ha⟩ := (left_exact_all_degrees m (homEEquiv F)).mp hz
    refine ⟨homEEquiv.symm a,?_⟩
    apply homEEquiv.injective
    rw [homEEquiv_diff,homEEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨G,rfl⟩
    apply homEEquiv.injective
    rw [homEEquiv_diff,homEEquiv_diff,map_zero]
    exact (left_exact_all_degrees m).apply_apply_eq_zero _

theorem homDiff_consecutive_zero (t : ℚ) (F : HomE) :
    homDiff (-2*t) (homDiff t F)=0 := by
  apply homEEquiv.injective
  rw [homEEquiv_diff,homEEquiv_diff,map_zero]
  obtain ⟨a,ha⟩ := ecIso.surjective (homEEquiv F)
  rw [← ha,leftDiff_iso,leftDiff_iso,← ecIso.map_zero]
  exact congrArg ecIso (left_consecutive_zero t a)

theorem homSimpleRegular_zero (F : Simple →ₗ[A] A) : F=0 := by
  have h : F.comp augmentation=0 := by
    apply homInitial_injective
    rw [map_zero]
    apply LinearMap.ext
    intro x
    change F (augmentation (initialMap x))=0
    rw [augmentation_exact.apply_apply_eq_zero,map_zero]
  apply LinearMap.ext
  intro x
  obtain ⟨a,rfl⟩ := augmentation_surjective x
  exact LinearMap.congr_fun h a

def homTwoShortComplex : ShortComplex (ModuleCat Aᵐᵒᵖ) :=
  ShortComplex.moduleCatMk (homDiff 1) (homDiff (-2)) (by
    apply LinearMap.ext
    intro F
    simpa using homDiff_consecutive_zero 1 F)

def homTwoShortComplexIso : homTwoShortComplex ≅ dualTwoShortComplex :=
  ShortComplex.isoMk homEEquiv.toModuleIso
    homEEquiv.toModuleIso homEEquiv.toModuleIso
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro F; exact (homEEquiv_diff 1 F).symm)
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro F; exact (homEEquiv_diff (-2) F).symm)

def homTwoHomologyIso : homTwoShortComplex.homology ≅
    ModuleCat.of Aᵐᵒᵖ RightCharacterModule :=
  (ShortComplex.homologyFunctor (ModuleCat Aᵐᵒᵖ)).mapIso homTwoShortComplexIso ≪≫
    dualTwoHomologyIso

end
end TachikawaCharZero.Resolution
