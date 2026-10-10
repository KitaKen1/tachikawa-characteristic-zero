import TachikawaCharZero.SoclePerfectObstruction
import OAI.RingTheory.Tachikawa.InducedRegular

/-! Induce the actual B_theta projective resolution, retaining the rational
signed twist required by the trace obstruction. The character map defines
an actual induced representation map by the induction/restriction unit.
Its socle composite recovers eta after restriction, and consequently has
no bounded finite-projective E-enveloping derived factorization.
This does not yet assert nonzero evaluated stable lifts. -/
namespace TachikawaCharZero.InducedTwistedSocle
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open ScalingSocle SocleBimodule
open scoped TensorProduct ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard

section Generic
variable {k R A : Type} [Field k] [Ring R] [Ring A] [Algebra k R] [Algebra k A]

def extendResolutionMap (φ : R →ₐ[k] A) {N : ModuleCat R}
    (P : ProjectiveResolution N) (V : ModuleCat A)
    (f : N ⟶ (AlgebraInduction.res φ).obj V) :=
  AlgebraInduction.complexExtend φ (.up ℤ)
    (P.π' ≫ (CochainComplex.singleFunctor (ModuleCat R) 0).map f ≫
      (singleMapHomologicalComplex (AlgebraInduction.res φ) (.up ℤ) 0).inv.app V)

theorem extendResolutionMap_unit (φ : R →ₐ[k] A) {N : ModuleCat R}
    (P : ProjectiveResolution N) (V : ModuleCat A)
    (f : N ⟶ (AlgebraInduction.res φ).obj V) :
    AlgebraInduction.complexUnit φ (.up ℤ) P.cochainComplex ≫
        (AlgebraInduction.complexRestriction φ (.up ℤ)).map (extendResolutionMap φ P V f) =
      P.π' ≫ (CochainComplex.singleFunctor (ModuleCat R) 0).map f ≫
        (singleMapHomologicalComplex (AlgebraInduction.res φ) (.up ℤ) 0).inv.app V :=
  AlgebraInduction.complexUnit_extend φ (.up ℤ) _

theorem extendResolutionMap_square (φ : R →ₐ[k] A) {N : ModuleCat R}
    (P : ProjectiveResolution N) (V U : ModuleCat A) (D : ModuleCat R)
    (f : N ⟶ (AlgebraInduction.res φ).obj V) (v : V ⟶ U)
    (b : (AlgebraInduction.res φ).obj U ⟶ D) :
    AlgebraInduction.complexUnit φ (.up ℤ) P.cochainComplex ≫
        (AlgebraInduction.complexRestriction φ (.up ℤ)).map
          (extendResolutionMap φ P V f ≫ (CochainComplex.singleFunctor _ 0).map v) ≫
        (singleMapHomologicalComplex (AlgebraInduction.res φ) (.up ℤ) 0).hom.app U ≫
        (CochainComplex.singleFunctor _ 0).map b =
      P.π' ≫ (CochainComplex.singleFunctor _ 0).map
        (f ≫ (AlgebraInduction.res φ).map v ≫ b) := by
  rw [Functor.map_comp]
  rw [← Category.assoc,← Category.assoc,← Category.assoc]
  rw [extendResolutionMap_unit]
  simp only [Category.assoc]
  have hn := (singleMapHomologicalComplex (AlgebraInduction.res φ) (.up ℤ) 0).hom.naturality v
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc
    ((AlgebraInduction.complexRestriction φ (.up ℤ)).map
      ((CochainComplex.singleFunctor _ 0).map v)), hn]
  simp only [Iso.inv_hom_id_app_assoc,Functor.map_comp,Category.assoc]
end Generic

-- Keep the native semiring projections when specializing ring-based adjunctions.
-- This avoids repeatedly comparing the large tensor-ring structure diamonds.
local instance beRing : Ring BE :=
  { (inferInstance : Ring BE) with toSemiring := (inferInstance : Semiring BE) }
local instance eeRing : Ring EE :=
  { (inferInstance : Ring EE) with toSemiring := (inferInstance : Semiring EE) }

abbrev resolution := TwistedDerivedObstruction.sourceResolution
abbrev inductionFunctor := AlgebraInduction.functor (k := ℚ) (R := BE) (S := EE) inclusionBE
abbrev restrictionComplex := restriction.mapHomologicalComplex (.up ℤ)
abbrev singleE := CochainComplex.singleFunctor (ModuleCat EE) 0
abbrev singleB := CochainComplex.singleFunctor (ModuleCat BE) 0
abbrev comparison := singleMapHomologicalComplex restriction (.up ℤ) 0
abbrev inducedComplex : CochainComplex (ModuleCat EE) ℤ :=
  (inductionFunctor.mapHomologicalComplex (.up ℤ)).obj
  resolution.cochainComplex

def unit :=
  AlgebraInduction.complexUnit (k := ℚ) (R := BE) (S := EE)
    inclusionBE (.up ℤ) resolution.cochainComplex

def preRepresentation :=
  resolution.π' ≫ singleB.map restrictedCharacterMap ≫ comparison.inv.app S

def representation :=
  extendResolutionMap (k := ℚ) (R := BE) (A := EE) inclusionBE
    (N := TwistedBimoduleObstruction.U) resolution S
    restrictedCharacterMap

def inducedSocleMap (H : ℚ) (hH : H ≠ 0) : inducedComplex ⟶ singleE.obj (UH H hH) :=
  representation ≫ singleE.map (socleMap H hH)

def rhoSingle (H : ℚ) (hH : H ≠ 0) :
    restrictionComplex.obj (singleE.obj (UH H hH)) ⟶ TwistedDerivedObstruction.targetSingle :=
  comparison.hom.app (UH H hH) ≫ singleB.map (rhoMap H hH)

theorem unit_representation : unit ≫ restrictionComplex.map representation=preRepresentation :=
  extendResolutionMap_unit (k := ℚ) (R := BE) (A := EE) inclusionBE
    (N := TwistedBimoduleObstruction.U) resolution S
    restrictedCharacterMap

theorem unit_socle_eta (H : ℚ) (hH : H ≠ 0) :
    unit ≫ restrictionComplex.map (inducedSocleMap H hH) ≫ rhoSingle H hH =
      resolution.π' ≫ singleB.map TwistedBimoduleObstruction.etaMap := by
  have h := extendResolutionMap_square (k := ℚ) (R := BE) (A := EE) inclusionBE
    (N := TwistedBimoduleObstruction.U) resolution S (UH H hH) TwistedBimoduleObstruction.D
    restrictedCharacterMap (socleMap H hH) (rhoMap H hH)
  simp only [restricted_character_socle_eta] at h
  dsimp only [representation,inducedSocleMap,rhoSingle]
  with_unfolding_all exact h

theorem inducedSocle_not_bounded_projective_factor (H : ℚ) (hH : H ≠ 0)
    (P : CochainComplex (ModuleCat EE) ℤ)
    (hfin : ∀ i, Module.Finite EE (P.X i))
    (hproj : ∀ i, Module.Projective EE (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj inducedComplex ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (singleE.obj (UH H hH))) :
    α ≫ β ≠ DerivedCategory.Q.map (inducedSocleMap H hH) := by
  intro h
  obtain ⟨Q,f,hf,hp,hf',hb⟩ := RestrictedPerfect.bounded_replacement P hfin hproj l u hbound
  let := hf
  let a := inv (DerivedCategory.Q.map resolution.π') ≫ DerivedCategory.Q.map unit ≫
    exactDerivedHom restriction α ≫ inv (DerivedCategory.Q.map f)
  let b := DerivedCategory.Q.map f ≫ exactDerivedHom restriction β ≫
    DerivedCategory.Q.map (rhoSingle H hH)
  apply TwistedDerivedObstruction.eta_not_bounded_projective_factor
    Q hf' hp (l-8) u hb a b
  calc
    a ≫ b = inv (DerivedCategory.Q.map resolution.π') ≫ DerivedCategory.Q.map unit ≫
        exactDerivedHom restriction (α ≫ β) ≫ DerivedCategory.Q.map (rhoSingle H hH) := by
      simp only [a,b,Category.assoc,IsIso.inv_hom_id_assoc,exactDerivedHom_comp]
    _ = inv (DerivedCategory.Q.map resolution.π') ≫ DerivedCategory.Q.map unit ≫
        DerivedCategory.Q.map (restrictionComplex.map (inducedSocleMap H hH)) ≫
          DerivedCategory.Q.map (rhoSingle H hH) := by rw [h,exactDerivedHom_map]
    _ = inv (DerivedCategory.Q.map resolution.π') ≫
        DerivedCategory.Q.map (resolution.π' ≫ singleB.map TwistedBimoduleObstruction.etaMap) := by
      rw [← Functor.map_comp,← Functor.map_comp]
      congr 2
      exact unit_socle_eta H hH
    _ = DerivedCategory.Q.map (singleB.map TwistedBimoduleObstruction.etaMap) := by
      simp only [Functor.map_comp,IsIso.inv_hom_id_assoc]

theorem resolution_term_finite (n : ℕ) : Module.Finite BE (resolution.complex.X n) := by
  change Module.Finite BE (TwistedDerivedObstruction.sourceFinite.posTerm n)
  infer_instance

theorem induced_term_finite (i : ℤ) : Module.Finite EE (inducedComplex.X i) := by
  let : Module.Finite BE (resolution.cochainComplex.X i) :=
    finite_resolution_cochain resolution resolution_term_finite i
  let : IsScalarTower ℚ BE (resolution.cochainComplex.X i) :=
    ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ) (resolution.cochainComplex.X i)
  let : FiniteDimensional ℚ (resolution.cochainComplex.X i) := Module.Finite.trans BE _
  let : FiniteDimensional ℚ (inductionFunctor.obj (resolution.cochainComplex.X i)) := inferInstance
  change Module.Finite EE (inductionFunctor.obj (resolution.cochainComplex.X i))
  let : IsScalarTower ℚ EE (inductionFunctor.obj (resolution.cochainComplex.X i)) :=
    ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ)
      (inductionFunctor.obj (resolution.cochainComplex.X i))
  exact Module.Finite.of_restrictScalars_finite ℚ EE _

instance induced_projective (i : ℤ) : Projective (inducedComplex.X i) := by
  let : Module.Finite BE (resolution.cochainComplex.X i) :=
    finite_resolution_cochain resolution resolution_term_finite i
  change Projective (inductionFunctor.obj (resolution.cochainComplex.X i))
  infer_instance

theorem induced_term_projective (i : ℤ) : Module.Projective EE (inducedComplex.X i) :=
  inferInstance

instance induced_bounded : inducedComplex.IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact inductionFunctor.map_isZero
    (resolution.cochainComplex.isZero_of_isStrictlyLE 0 i hi)

instance induced_isKProjective : inducedComplex.IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

end
end TachikawaCharZero.InducedTwistedSocle
