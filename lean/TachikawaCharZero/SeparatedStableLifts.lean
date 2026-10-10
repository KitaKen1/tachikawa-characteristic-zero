import TachikawaCharZero.InducedHighExactness

/-! The actual separated representation/socle lifts have nonzero stable
cokernel classes in every degree at least five. This is an E-enveloping
stable assertion; fixed Y and nonzero tensor-Hom evaluation remain separate.
The actual finite source cokernels are also nonprojective in this range. -/
namespace TachikawaCharZero.SeparatedStableLifts
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa
open ScalingSocle InducedTwistedSocle TwistedSocleLifts
attribute [local instance] HasDerivedCategory.standard
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

theorem separated_lifts_stable_ne_zero (H : ℚ) (hH : H ≠ 0)
    (a : inducedComplex ⟶ finiteS.projectiveResolution.cochainComplex)
    (b : finiteS.projectiveResolution.cochainComplex ⟶
      (finiteU H hH).projectiveResolution.cochainComplex)
    (hab : DerivedCategory.Q.map (a ≫ b) ≫
      DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap H hH)) (n : ℕ) (hn : 5 ≤ n) :
    stableClass (k := ℚ) (CokerAt.map (reflectCochainMap a) n) ≠ 0 ∧
      stableClass (k := ℚ) (CokerAt.map (reflectCochainMap b) n) ≠ 0 := by
  have h := InducedHighExactness.lift_stable_ne_zero H hH (a ≫ b) hab n hn
  have hc : reflectCochainMap (a ≫ b) = reflectCochainMap a ≫ reflectCochainMap b := rfl
  constructor
  · intro ha
    apply h
    apply (stableClass_eq_zero_iff _).mpr
    rw [hc, CokerAt.map_comp]
    exact projectiveFactors_postcomp ((stableClass_eq_zero_iff _).mp ha) _
  · intro hb
    apply h
    apply (stableClass_eq_zero_iff _).mpr
    rw [hc, CokerAt.map_comp]
    exact projectiveFactors_precomp ((stableClass_eq_zero_iff _).mp hb) _

theorem exists_separated_stable_lifts (H : ℚ) (hH : H ≠ 0) :
    ∃ (a : inducedComplex ⟶ finiteS.projectiveResolution.cochainComplex)
      (b : finiteS.projectiveResolution.cochainComplex ⟶
        (finiteU H hH).projectiveResolution.cochainComplex),
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map finiteS.projectiveResolution.π' =
        DerivedCategory.Q.map representation ∧
      DerivedCategory.Q.map b ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map finiteS.projectiveResolution.π' ≫
          DerivedCategory.Q.map (singleE.map (SocleBimodule.socleMap H hH)) ∧
      DerivedCategory.Q.map (a ≫ b) ≫
          DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap H hH) ∧
      ∀ n : ℕ, 5 ≤ n →
        stableClass (k := ℚ) (CokerAt.map (reflectCochainMap a) n) ≠ 0 ∧
          stableClass (k := ℚ) (CokerAt.map (reflectCochainMap b) n) ≠ 0 := by
  obtain ⟨a,b,ha,hb,hab⟩ := exists_separated_lifts H hH
  exact ⟨a,b,ha,hb,hab,fun n hn => separated_lifts_stable_ne_zero H hH a b hab n hn⟩

theorem sourceCoker_nonprojective (n : ℕ) (hn : 5 ≤ n) :
    ¬ Module.Projective EE (CokerAt (reflectCochain inducedComplex) n) := by
  obtain ⟨f,_,h⟩ := InducedHighExactness.exists_stable_lift 1 (by norm_num)
  intro hp
  apply h n hn
  apply (stableClass_eq_zero_iff _).mpr
  refine ⟨ModuleCat.of EE (CokerAt (reflectCochain inducedComplex) n),
    TwistedStableGate.source_coker_finite n,hp,LinearMap.id,
    CokerAt.map (reflectCochainMap f) n,?_⟩
  exact LinearMap.comp_id _

end
end TachikawaCharZero.SeparatedStableLifts
