import TachikawaCharZero.InducedTwistedSocle
import OAI.RingTheory.Tachikawa.FiniteResolutionLift

/-! Actual cochain lifts of the signed induced representation and socle
maps over the rational E-enveloping algebra. Their derived augmentation
identities and absence of bounded perfect factorizations are proved.
High-cokernel exactness, stable nonzero classes, fixed Y comparison and
evaluation remain additional obligations. -/
namespace TachikawaCharZero.TwistedSocleLifts
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open ScalingSocle SocleBimodule InducedTwistedSocle
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard

local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def finiteS : FiniteModule ℚ EE := by
  let : FiniteDimensional ℚ S := inferInstanceAs
    (FiniteDimensional ℚ (HomBimodule.obj (k := ℚ) X X))
  let : IsScalarTower ℚ EE S := ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ) S
  let : Module.Finite EE S := Module.Finite.of_restrictScalars_finite ℚ EE S
  exact ⟨S,inferInstance⟩

def finiteU (H : ℚ) (hH : H ≠ 0) : FiniteModule ℚ EE := by
  let : FiniteDimensional ℚ (UH H hH) := inferInstanceAs
    (FiniteDimensional ℚ (Enveloping.twistedRegular (scaling H hH)))
  let : IsScalarTower ℚ EE (UH H hH) :=
    ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ) (UH H hH)
  let : Module.Finite EE (UH H hH) := Module.Finite.of_restrictScalars_finite ℚ EE _
  exact ⟨UH H hH,inferInstance⟩

theorem exists_socle_lift (H : ℚ) (hH : H ≠ 0) :
    ∃ f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap H hH) :=
  finiteResolutionLift inducedComplex (finiteU H hH)
    (DerivedCategory.Q.map (inducedSocleMap H hH))

theorem exists_separated_lifts (H : ℚ) (hH : H ≠ 0) :
    ∃ (a : inducedComplex ⟶ finiteS.projectiveResolution.cochainComplex)
      (b : finiteS.projectiveResolution.cochainComplex ⟶
        (finiteU H hH).projectiveResolution.cochainComplex),
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map finiteS.projectiveResolution.π' =
        DerivedCategory.Q.map representation ∧
      DerivedCategory.Q.map b ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map finiteS.projectiveResolution.π' ≫
          DerivedCategory.Q.map (singleE.map (socleMap H hH)) ∧
      DerivedCategory.Q.map (a ≫ b) ≫
          DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap H hH) := by
  obtain ⟨a,ha⟩ := finiteResolutionLift inducedComplex finiteS (DerivedCategory.Q.map representation)
  obtain ⟨b,hb⟩ := finiteResolutionLift finiteS.projectiveResolution.cochainComplex
    (finiteU H hH) (DerivedCategory.Q.map finiteS.projectiveResolution.π' ≫
      DerivedCategory.Q.map (singleE.map (socleMap H hH)))
  refine ⟨a,b,ha,hb,?_⟩
  exact lift_composite_eq DerivedCategory.Q a b _ _ _ _ ha hb

theorem lift_not_bounded_projective_factor (H : ℚ) (hH : H ≠ 0)
    (f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex)
    (hf : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
      DerivedCategory.Q.map (inducedSocleMap H hH))
    (P : CochainComplex (ModuleCat EE) ℤ)
    (hfin : ∀ i, Module.Finite EE (P.X i))
    (hproj : ∀ i, Module.Projective EE (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj inducedComplex ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶
      DerivedCategory.Q.obj (finiteU H hH).projectiveResolution.cochainComplex) :
    α ≫ β ≠ DerivedCategory.Q.map f := by
  intro h
  apply inducedSocle_not_bounded_projective_factor H hH P hfin hproj l u hbound α
    (β ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π')
  rw [← Category.assoc,h,hf]

end
end TachikawaCharZero.TwistedSocleLifts
