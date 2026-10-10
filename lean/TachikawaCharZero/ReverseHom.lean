import TachikawaCharZero.SignedReverseComplex
import TachikawaCharZero.RegularExt
import TachikawaCharZero.InducedHomology
import OAI.RingTheory.Tachikawa.NakayamaTransfer

/-! The Hom/Nakayama side of the signed rational reverse comparison.
The exceptional degree-two class is normalized by the v coefficient. -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
open OAI.ArExplicit TachikawaCharZero.Resolution
open OAI.Tachikawa (Nakayama)

theorem reverseCoeff_left_ne_zero (n : ℕ) : 1 - reverseCoeff n ≠ 0 := by
  intro h
  have hi : ((-2:ℚ)^(n+2))⁻¹=1 := by change reverseCoeff n=1; linarith
  have hp := congrArg (fun z : ℚ => z⁻¹) hi
  simp only [inv_inv,inv_one] at hp
  exact resolution_left_coefficient_ne_zero (n+2) (by omega) (by rw [hp]; norm_num)

theorem reverseCoeff_left_next_ne_zero (n : ℕ) : 1 + 2 * reverseCoeff (n+1) ≠ 0 := by
  have he : 1+2*reverseCoeff (n+1)=1-reverseCoeff n := by
    rw [← reverseCoeff_step n]
    ring
  rw [he]
  exact reverseCoeff_left_ne_zero n

theorem homDiff_exact_general (t : ℚ) (ht : 1-t≠0) (ht' : 1+2*t≠0) :
    Function.Exact (homDiff t) (homDiff (-2*t)) := by
  intro F
  constructor
  · intro h
    obtain ⟨a,ha⟩ := ecIso.surjective (homEEquiv F)
    have hz : leftD (-2*t) a=0 := by
      have he : leftDiff (-2*t) (homEEquiv F)=0 := by
        rw [← homEEquiv_diff,h,map_zero]
      rw [← ha,leftDiff_iso,← ecIso.map_zero] at he
      exact ecIso.injective he
    obtain ⟨b,hb⟩ := (left_exact_coordinates t ht ht' a).mp hz
    refine ⟨homEEquiv.symm (ecIso b), ?_⟩
    apply homEEquiv.injective
    rw [homEEquiv_diff,homEEquiv.apply_symm_apply,leftDiff_iso,hb,ha]
  · rintro ⟨G,rfl⟩
    exact homDiff_consecutive_zero t G

theorem hom_reverse_exact (n : ℕ) : Function.Exact (homDiff (reverseCoeff (n+1)))
    (homDiff (reverseCoeff n)) := by
  rw [← reverseCoeff_step n]
  exact homDiff_exact_general _ (reverseCoeff_left_ne_zero (n+1))
    (reverseCoeff_left_next_ne_zero n)

theorem f_fixed_t : vertexF * BaseAlgebra.basisVector (2:ℚ) .t =
    BaseAlgebra.basisVector (2:ℚ) .t := BaseAlgebra.basis_mul 2 .f .t

theorem e_fixed_v : vertexE * BaseAlgebra.basisVector (2:ℚ) .v =
    BaseAlgebra.basisVector (2:ℚ) .v := BaseAlgebra.basis_mul 2 .e .v

def lambdaT : EC →ₗ[Aᵐᵒᵖ] FC := Corner.mulLeft (BaseAlgebra.basisVector 2 .t) f_fixed_t
def lambdaV : FC →ₗ[Aᵐᵒᵖ] EC := Corner.mulLeft (BaseAlgebra.basisVector 2 .v) e_fixed_v

theorem lambdaT_iso (a : V) : lambdaT (ecIso a) = fcIso ![0,a 0,a 1+4*a 2,3*a 4] := by
  apply Subtype.ext
  change BaseAlgebra.basisVector 2 .t * ecEmbed a = fcEmbed _
  ext i
  cases i <;> norm_num [ecEmbed,fcEmbed,BaseAlgebra.product]

theorem lambdaV_iso (a : V₀) : lambdaV (fcIso a) = ecIso ![0,0,0,2*a 1,0,a 0] := by
  apply Subtype.ext
  change BaseAlgebra.basisVector 2 .v * fcEmbed a = ecEmbed _
  ext i
  cases i <;> simp [ecEmbed,fcEmbed,BaseAlgebra.product]

theorem lambdaT_exact : Function.Exact (leftDiff (1/4)) lambdaT := by
  intro a
  obtain ⟨a,rfl⟩ := ecIso.surjective a
  constructor
  · intro h
    rw [lambdaT_iso,← fcIso.map_zero] at h
    have hh:=fcIso.injective h
    have h0 : a 0=0 := by have hi:=congrFun hh 1; simpa using hi
    have h2 : a 2= -(1/4)*a 1 := by
      have hi:=congrFun hh 2
      change a 1+4*a 2=0 at hi
      linarith
    have h4 : a 4=0 := by have hi:=congrFun hh 3; simpa using hi
    refine ⟨ecIso ![a 1,0,a 3/2,0,4*a 5/3,0], ?_⟩
    rw [leftDiff_iso]
    apply ecIso.injective.eq_iff.mpr
    ext i
    fin_cases i <;> norm_num [leftD,h0,h2,h4]
    all_goals ring
  · rintro ⟨b,hb⟩
    obtain ⟨b,rfl⟩ := ecIso.surjective b
    rw [← hb,leftDiff_iso,lambdaT_iso,← fcIso.map_zero]
    apply congrArg fcIso
    ext i
    fin_cases i <;> norm_num [leftD]
    ring

def homT : HomE →ₗ[Aᵐᵒᵖ] HomF where
  toFun F := F.comp rhoT
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homV : HomF →ₗ[Aᵐᵒᵖ] HomE where
  toFun F := F.comp rhoV
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homT_equiv (F : HomE) : homFEquiv (homT F)=lambdaT (homEEquiv F) :=
  Corner.homRightEquiv_precomp vertexF_idempotent vertexE_idempotent
    _ f_fixed_t t_fixed_by_e F

theorem homV_equiv (F : HomF) : homEEquiv (homV F)=lambdaV (homFEquiv F) :=
  Corner.homRightEquiv_precomp vertexE_idempotent vertexF_idempotent
    _ e_fixed_v v_fixed_by_f F

theorem homT_exact : Function.Exact (homDiff (reverseCoeff 0)) homT := by
  rw [reverseCoeff_zero]
  intro F
  constructor
  · intro h
    have hz : lambdaT (homEEquiv F)=0 := by rw [← homT_equiv,h,map_zero]
    obtain ⟨a,ha⟩ := (lambdaT_exact _).mp hz
    refine ⟨homEEquiv.symm a, ?_⟩
    apply homEEquiv.injective
    rw [homEEquiv_diff,homEEquiv.apply_symm_apply,ha]
  · rintro ⟨G,rfl⟩
    apply homFEquiv.injective
    rw [homT_equiv,homEEquiv_diff,map_zero]
    exact lambdaT_exact.apply_apply_eq_zero _

theorem nu_reverse_exact (n : ℕ) : Function.Exact
    (OAI.Tachikawa.Nakayama.map (k:=ℚ) (ceDiff (reverseCoeff n)))
    (OAI.Tachikawa.Nakayama.map (ceDiff (reverseCoeff (n+1)))) :=
  OAI.Tachikawa.exact_dual ((homDiff (reverseCoeff (n+1))).restrictScalars ℚ)
    ((homDiff (reverseCoeff n)).restrictScalars ℚ) (hom_reverse_exact n)

theorem nu_reverse_top_exact : Function.Exact
    (OAI.Tachikawa.Nakayama.map (k:=ℚ) rhoT)
    (OAI.Tachikawa.Nakayama.map (ceDiff (reverseCoeff 0))) :=
  OAI.Tachikawa.exact_dual ((homDiff (reverseCoeff 0)).restrictScalars ℚ)
    (homT.restrictScalars ℚ) homT_exact

def fHom : HomF := homFEquiv.symm (fcIso ![1,0,0,0])

theorem fHom_rhoV : homV fHom=vHom := by
  apply homEEquiv.injective
  rw [homV_equiv,fHom,homFEquiv.apply_symm_apply,lambdaV_iso,
    vHom,homEEquiv.apply_symm_apply]
  norm_num

theorem homTop_decompose (F : HomF) : ∃ G : HomE,
    F=homT G + ((homFEquiv F:A).coeff .f) • fHom := by
  obtain ⟨a,ha⟩ := fcIso.surjective (homFEquiv F)
  refine ⟨homEEquiv.symm (ecIso ![a 1,a 2,0,0,a 3/3,0]), ?_⟩
  apply homFEquiv.injective
  rw [map_add,LinearMapClass.map_smul_of_tower homFEquiv,
    homT_equiv,homEEquiv.apply_symm_apply,
    lambdaT_iso,fHom,homFEquiv.apply_symm_apply,← ha]
  change fcIso a=fcIso _ + a 0 • fcIso ![1,0,0,0]
  rw [← fcIso.map_smul,← fcIso.map_add]
  apply congrArg fcIso
  ext i
  fin_cases i <;> norm_num
  ring

def nuTopCycle : Nakayama ℚ A Cf where
  toFun F := (homFEquiv F:A).coeff .f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def nuTwoCycle : Nakayama ℚ A Ce where
  toFun F := (homEEquiv F:A).coeff .v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem nuTwoCycle_closed : OAI.Tachikawa.Nakayama.map (ceDiff 1) nuTwoCycle=0 := by
  apply LinearMap.ext
  intro F
  exact homDiff_one_v_zero F

theorem nuV_nuTwoCycle : OAI.Tachikawa.Nakayama.map rhoV nuTwoCycle=nuTopCycle := by
  apply LinearMap.ext
  intro F
  change (homEEquiv (homV F):A).coeff .v=(homFEquiv F:A).coeff .f
  rw [homV_equiv]
  obtain ⟨a,ha⟩ := fcIso.surjective (homFEquiv F)
  rw [← ha,lambdaV_iso]
  rfl

theorem nuTopCycle_description (ψ : Nakayama ℚ A Cf)
    (hψ : OAI.Tachikawa.Nakayama.map rhoT ψ=0) : ψ=ψ fHom • nuTopCycle := by
  apply LinearMap.ext
  intro F
  obtain ⟨G,hG⟩ := homTop_decompose F
  have hh : ψ (homT G)=0 := LinearMap.congr_fun hψ G
  calc
    ψ F = ψ (homT G + ((homFEquiv F:A).coeff .f) • fHom) := congrArg ψ hG
    _ = ((homFEquiv F:A).coeff .f) * ψ fHom := by
      rw [map_add,hh,zero_add,map_smul]; rfl
    _ = (ψ fHom • nuTopCycle) F := mul_comm _ _

theorem nuTwo_boundary (ψ : Nakayama ℚ A Ce)
    (hψ : OAI.Tachikawa.Nakayama.map (ceDiff 1) ψ=0) (hv : ψ vHom=0) :
    ∃ ξ, OAI.Tachikawa.Nakayama.map (ceDiff (-2)) ξ=ψ := by
  change Module.Dual ℚ HomE at ψ
  change ψ vHom=0 at hv
  have hr : ψ ∈ LinearMap.range ((homDiff (-2)).restrictScalars ℚ).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,Submodule.mem_dualAnnihilator]
    intro F hF
    have hker : leftDiff (-2) (homEEquiv F)=0 := by
      rw [← homEEquiv_diff]
      change homDiff (-2) F=0 at hF
      rw [hF,map_zero]
    let a : DualTwoCycles := ⟨homEEquiv F,hker⟩
    have ha := Induced.right_cycle_decompose a
    let G := homEEquiv.symm (ecIso ![(homEEquiv F:A).coeff .x,0,
      (homEEquiv F:A).coeff .z/2,0,0,0])
    have he : F=homDiff 1 G + (homEEquiv F:A).coeff .v • vHom := by
      apply homEEquiv.injective
      dsimp only [G]
      rw [map_add,LinearMapClass.map_smul_of_tower homEEquiv,homEEquiv_diff,
        homEEquiv.apply_symm_apply,vHom,homEEquiv.apply_symm_apply]
      exact ha
    have hz : ψ (homDiff 1 G)=0 := LinearMap.congr_fun hψ G
    rw [he,map_add,hz,zero_add,map_smul,hv,smul_zero]
  exact hr

theorem nuV_cycles_injective (ψ : Nakayama ℚ A Ce)
    (hψ : OAI.Tachikawa.Nakayama.map (ceDiff 1) ψ=0)
    (hV : OAI.Tachikawa.Nakayama.map rhoV ψ=0) :
    ∃ ξ, OAI.Tachikawa.Nakayama.map (ceDiff (-2)) ξ=ψ := by
  apply nuTwo_boundary ψ hψ
  have h:=LinearMap.congr_fun hV fHom
  change ψ (homV fHom)=0 at h
  rw [fHom_rhoV] at h
  exact h

theorem nuV_cycles_surjective (ψ : Nakayama ℚ A Cf)
    (hψ : OAI.Tachikawa.Nakayama.map rhoT ψ=0) : ∃ ξ : Nakayama ℚ A Ce,
    OAI.Tachikawa.Nakayama.map (ceDiff 1) ξ=0 ∧
    OAI.Tachikawa.Nakayama.map rhoV ξ=ψ := by
  refine ⟨ψ fHom • nuTwoCycle, ?_, ?_⟩
  · rw [LinearMap.map_smul_of_tower,nuTwoCycle_closed,smul_zero]
  · rw [LinearMap.map_smul_of_tower,nuV_nuTwoCycle]
    exact (nuTopCycle_description ψ hψ).symm

end
end TachikawaCharZero.ReverseCorner
