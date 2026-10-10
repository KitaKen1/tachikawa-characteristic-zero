import TachikawaCharZero.DualComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Degree two of the actual rational dual complex is the right character
at f. In particular the right action, not just the vector-space dimension,
is identified. The quotient construction adapts the generic pattern in
OpenAI Math's Tachikawa/Corner.lean, fixed at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.Resolution
noncomputable section
open OAI.ArExplicit
open CategoryTheory

def rightCharacter : Aᵐᵒᵖ →ₐ[ℚ] ℚ where
  toFun a := character a.unop
  map_zero' := map_zero character
  map_one' := map_one character
  map_add' a b := map_add character a.unop b.unop
  map_mul' a b := by change character (b.unop*a.unop)=_; rw [map_mul,mul_comm]
  commutes' c := character.commutes c

def RightCharacterModule := ℚ
instance : AddCommGroup RightCharacterModule := inferInstanceAs (AddCommGroup ℚ)
instance : Module ℚ RightCharacterModule := inferInstanceAs (Module ℚ ℚ)
instance : Module Aᵐᵒᵖ RightCharacterModule :=
  Module.compHom RightCharacterModule rightCharacter.toRingHom
instance : IsScalarTower ℚ Aᵐᵒᵖ RightCharacterModule :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change rightCharacter (algebraMap ℚ Aᵐᵒᵖ r) • x = r • x
    rw [AlgHom.commutes]
    rfl

abbrev DualTwoCycles := LinearMap.ker (leftDiff (-2))

theorem dualTwo_coordinates (a : DualTwoCycles) :
    (a.val:A).coeff .e=0 ∧ (a.val:A).coeff .y= -(a.val:A).coeff .x ∧
      (a.val:A).coeff .u=0 := by
  obtain ⟨x,hx⟩ := ecIso.surjective a.val
  have h := a.property
  change leftDiff (-2) a.val=0 at h
  rw [← hx,leftDiff_iso,← ecIso.map_zero] at h
  have hh := ecIso.injective h
  have h0 : x 0=0 := by have h:=congrFun hh 1; simpa [leftD] using h
  have h2 : x 2= -x 1 := by
    have h:=congrFun hh 3
    norm_num [leftD] at h
    linarith
  have h4 : x 4=0 := by have h:=congrFun hh 5; norm_num [leftD] at h; exact h
  rw [← hx]
  exact ⟨h0,h2,h4⟩

def dualTwoAug : DualTwoCycles →ₗ[Aᵐᵒᵖ] RightCharacterModule where
  toFun a := (a.val:A).coeff .v
  map_add' _ _ := rfl
  map_smul' b a := by
    obtain ⟨h0,h2,h4⟩ := dualTwo_coordinates a
    change ((a.val:A)*b.unop).coeff .v = b.unop.coeff .f*(a.val:A).coeff .v
    simp [BaseAlgebra.product,h0,h2,h4]
    ring

def dualTwoBoundary : EC →ₗ[Aᵐᵒᵖ] DualTwoCycles :=
  (leftDiff 1).codRestrict _ (fun a => by
    obtain ⟨a,rfl⟩ := ecIso.surjective a
    change leftDiff (-2) (leftDiff 1 (ecIso a))=0
    rw [leftDiff_iso,leftDiff_iso,← ecIso.map_zero]
    simpa using congrArg ecIso (left_consecutive_zero 1 a))

theorem dualTwoAug_surjective : Function.Surjective dualTwoAug := by
  intro c
  refine ⟨⟨ecIso ![0,0,0,0,0,(show ℚ from c)],?_⟩,rfl⟩
  change leftDiff (-2) _=0
  rw [leftDiff_iso,← ecIso.map_zero]
  apply congrArg ecIso
  ext i
  fin_cases i <;> norm_num [leftD]

theorem dualTwoAug_exact : Function.Exact dualTwoBoundary dualTwoAug := by
  intro a
  constructor
  · intro hv
    obtain ⟨h0,h2,h4⟩ := dualTwo_coordinates a
    change (a.val:A).coeff .v=0 at hv
    refine ⟨ecIso ![(a.val:A).coeff .x,0,(a.val:A).coeff .z/2,0,0,0],?_⟩
    apply Subtype.ext
    change leftDiff 1 _=a.val
    rw [leftDiff_iso]
    calc
      _ = ecIso (ecIso.symm a.val) := by
        apply congrArg ecIso
        ext i
        fin_cases i <;> simp [leftD,ecIso,h0,h2,h4,hv]
        ring
      _ = a.val := ecIso.apply_symm_apply _
  · rintro ⟨b,hb⟩
    obtain ⟨b,rfl⟩ := ecIso.surjective b
    rw [← hb]
    change (leftDiff 1 (ecIso b):A).coeff .v=0
    rw [leftDiff_iso]
    simp [ecIso,ecEmbed,leftD]

local instance : HasQuotient DualTwoCycles (Submodule Aᵐᵒᵖ DualTwoCycles) :=
  @Submodule.hasQuotient Aᵐᵒᵖ DualTwoCycles inferInstance inferInstance inferInstance

def dualTwoCohomologyEquiv :
    (DualTwoCycles ⧸ LinearMap.range dualTwoBoundary) ≃ₗ[Aᵐᵒᵖ] RightCharacterModule :=
  (Submodule.quotEquivOfEq _ _ dualTwoAug_exact.linearMap_ker_eq.symm).trans
    (dualTwoAug.quotKerEquivOfSurjective dualTwoAug_surjective)

theorem dualTwo_finrank :
    Module.finrank ℚ (DualTwoCycles ⧸ LinearMap.range dualTwoBoundary)=1 := by
  rw [(dualTwoCohomologyEquiv.restrictScalars ℚ).finrank_eq]
  exact Module.finrank_self ℚ

def dualTwoShortComplex : ShortComplex (ModuleCat Aᵐᵒᵖ) :=
  ShortComplex.moduleCatMk (leftDiff 1) (leftDiff (-2)) (by
    apply LinearMap.ext
    intro a
    exact (dualTwoBoundary a).property)

def dualTwoHomologyIso : dualTwoShortComplex.homology ≅
    ModuleCat.of Aᵐᵒᵖ RightCharacterModule :=
  dualTwoShortComplex.moduleCatHomologyIso ≪≫
    dualTwoCohomologyEquiv.toModuleIso

end
end TachikawaCharZero.Resolution
