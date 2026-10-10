import TachikawaCharZero.FixedBimoduleY
import OAI.RingTheory.Tachikawa.StableLiftDescent

/-! Descend actual nonzero degree-five stable compositions to the fixed Y.
This constructs actual maps from each scaling bimodule to Y and stable
nonzero detector compositions. Nonzero evaluation at X remains separate. -/
namespace TachikawaCharZero.FixedYLifts
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open ScalingSocle InducedTwistedSocle TwistedSocleLifts FixedBimoduleY
open scoped TensorProduct ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

theorem exists_Y_lift_with_nonzero_composition (H : ℚ) (hH : H ≠ 0) :
    ∃ (g : (finiteU H hH).obj ⟶ Y.obj)
      (psi : Y.obj ⟶ (finiteS.positive 1).obj),
      (g ≫ psi).hom ∉ projectiveFactors (k := ℚ) := by
  obtain ⟨a,b,_ha,_hb,hab⟩ := exists_separated_lifts H hH
  let aa := CokerAt.map (reflectCochainMap a) 5
  let bb := CokerAt.map (reflectCochainMap b) 5
  let eS := finiteS.reflectCokerPositiveEquiv 5
  let eU := (finiteU H hH).reflectCokerPositiveEquiv 5
  let phi : N.obj →ₗ[EE] (finiteS.positive 5).obj := eS.toLinearMap.comp aa
  let b' := (eU.toLinearMap.comp bb).comp eS.symm.toLinearMap
  have hn : bb.comp aa ∉ projectiveFactors (k := ℚ) := by
    intro hf
    apply InducedHighExactness.lift_stable_ne_zero H hH (a ≫ b) hab 5 (by omega)
    apply (stableClass_eq_zero_iff _).mpr
    change CokerAt.map (reflectCochainMap (a ≫ b)) 5 ∈ projectiveFactors (k := ℚ)
    have hc : reflectCochainMap (a ≫ b) = reflectCochainMap a ≫ reflectCochainMap b := rfl
    rw [hc,CokerAt.map_comp]
    exact hf
  have hbphi : b'.comp phi ∉ projectiveFactors (k := ℚ) := by
    intro hf
    have hback := projectiveFactors_postcomp hf eU.symm.toLinearMap
    have he : eU.symm.toLinearMap.comp (b'.comp phi) = bb.comp aa := by
      ext x
      change eU.symm (eU (bb (eS.symm (eS (aa x))))) = bb (aa x)
      rw [eS.symm_apply_apply,eU.symm_apply_apply]
    rw [he] at hback
    exact hn hback
  obtain ⟨beta,hbeta⟩ := form.exists_syzygy_postcomposition
    (finiteU H hH) N (finiteS.positive 5) 4 b' phi hbphi
  obtain ⟨g,psi,hg⟩ := FiniteModule.descend_nonzero_composition_iterated
    form (finiteU H hH) finiteS 4 N beta phi hbeta
  exact ⟨ModuleCat.ofHom (X := (finiteU H hH).obj) (Y := Y.obj) g,
    ModuleCat.ofHom (X := Y.obj) (Y := (finiteS.positive 1).obj) psi,hg⟩

def lift (H : ℚ) (hH : H ≠ 0) : (finiteU H hH).obj ⟶ Y.obj :=
  Classical.choose (exists_Y_lift_with_nonzero_composition H hH)

def detector (H : ℚ) (hH : H ≠ 0) : Y.obj ⟶ (finiteS.positive 1).obj :=
  Classical.choose (Classical.choose_spec (exists_Y_lift_with_nonzero_composition H hH))

theorem detector_composition_not_projectiveFactors (H : ℚ) (hH : H ≠ 0) :
    (lift H hH ≫ detector H hH).hom ∉ projectiveFactors (k := ℚ) :=
  Classical.choose_spec (Classical.choose_spec (exists_Y_lift_with_nonzero_composition H hH))

theorem lift_stable_ne_zero (H : ℚ) (hH : H ≠ 0) :
    stableClass (k := ℚ) (lift H hH).hom ≠ 0 := by
  intro hz
  apply detector_composition_not_projectiveFactors H hH
  exact projectiveFactors_postcomp ((stableClass_eq_zero_iff _).mp hz) (detector H hH).hom

end
end TachikawaCharZero.FixedYLifts
