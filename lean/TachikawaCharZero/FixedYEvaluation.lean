import TachikawaCharZero.FixedYLifts
import OAI.RingTheory.Tachikawa.StableEvaluation

/-! The actual rational fixed-Y lifts remain stably nonzero after tensoring
with X. The scaling twist fixes the X action, so its evaluation is X itself.
The paper stable-image identification and branch normalization are separate. -/
namespace TachikawaCharZero.FixedYEvaluation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open ScalingSocle SocleBimodule TwistedSocleLifts FixedBimoduleY
open scoped TensorProduct ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

theorem U_right_projective (H : ℚ) (hH : H ≠ 0) :
    Module.Projective Eᵐᵒᵖ (Enveloping.Obj (finiteU H hH).obj) := by
  change Module.Projective Eᵐᵒᵖ (Enveloping.Obj (UH H hH))
  infer_instance

theorem evaluated_lift_not_projectiveFactors (H : ℚ) (hH : H ≠ 0) :
    (Enveloping.evalMap X (FixedYLifts.lift H hH)).hom
      ∉ projectiveFactors (k := ℚ) := by
  let : Module.Projective Eᵐᵒᵖ (Enveloping.Obj Y.obj) := Y_side_projective.2
  let := U_right_projective H hH
  exact evaluation_nonzero_of_syzygy_composition Starting.E_form Starting.E_form
    X X (finiteU H hH) Y finiteS (LinearEquiv.refl _ _)
    (FixedYLifts.lift H hH).hom (FixedYLifts.detector H hH).hom
    (FixedYLifts.detector_composition_not_projectiveFactors H hH)

theorem evaluated_lift_stable_ne_zero (H : ℚ) (hH : H ≠ 0) :
    stableClass (k := ℚ) (Enveloping.evalMap X (FixedYLifts.lift H hH)).hom ≠ 0 := by
  exact mt (stableClass_eq_zero_iff _).mp (evaluated_lift_not_projectiveFactors H hH)

theorem scaling_fixed_X (H : ℚ) (hH : H ≠ 0) (r : E) (x : X) :
    scaling H hH r • x = r • x := by
  apply TensorProfile.groundEquiv.injective
  rw [ground_action,ground_action,character_scaling]

def uXIso (H : ℚ) (hH : H ≠ 0) :
    Enveloping.evalObj X (finiteU H hH).obj ≅ X :=
  Enveloping.twistedEvalIso (scaling H hH) X (scaling_fixed_X H hH)

def evaluatedLift (H : ℚ) (hH : H ≠ 0) : X ⟶ Enveloping.evalObj X Y.obj :=
  (uXIso H hH).inv ≫ Enveloping.evalMap X (FixedYLifts.lift H hH)

theorem evaluatedLift_not_projectiveFactors (H : ℚ) (hH : H ≠ 0) :
    (evaluatedLift H hH).hom ∉ projectiveFactors (k := ℚ) := by
  intro hh
  have hp := projectiveFactors_precomp hh (uXIso H hH).hom.hom
  apply evaluated_lift_not_projectiveFactors H hH
  convert hp using 1
  apply ModuleCat.hom_ext_iff.mp
  change Enveloping.evalMap X (FixedYLifts.lift H hH) =
    (uXIso H hH).hom ≫
      ((uXIso H hH).inv ≫ Enveloping.evalMap X (FixedYLifts.lift H hH))
  simp

theorem evaluatedLift_stable_ne_zero (H : ℚ) (hH : H ≠ 0) :
    stableClass (k := ℚ) (evaluatedLift H hH).hom ≠ 0 :=
  mt (stableClass_eq_zero_iff _).mp (evaluatedLift_not_projectiveFactors H hH)

theorem exists_nonzero_X_YX (H : ℚ) (hH : H ≠ 0) :
    ∃ f : X ⟶ Enveloping.evalObj X Y.obj,
      f.hom ∉ projectiveFactors (k := ℚ) :=
  ⟨evaluatedLift H hH,evaluatedLift_not_projectiveFactors H hH⟩

def g₂ : X ⟶ Enveloping.evalObj X Y.obj := evaluatedLift 2 (by norm_num)
def g₃ : X ⟶ Enveloping.evalObj X Y.obj := evaluatedLift 3 (by norm_num)

theorem g₂_stable_ne_zero : stableClass (k := ℚ) g₂.hom ≠ 0 :=
  evaluatedLift_stable_ne_zero 2 (by norm_num)

theorem g₃_stable_ne_zero : stableClass (k := ℚ) g₃.hom ≠ 0 :=
  evaluatedLift_stable_ne_zero 3 (by norm_num)

theorem evaluatedY_finite : Module.Finite E (Enveloping.evalObj X Y.obj) :=
  inferInstance

theorem evaluatedY_nonprojective : ¬ Module.Projective E (Enveloping.evalObj X Y.obj) := by
  intro hp
  apply evaluatedLift_not_projectiveFactors 2 (by norm_num)
  exact ⟨Enveloping.evalObj X Y.obj,evaluatedY_finite,hp,
    (evaluatedLift 2 (by norm_num)).hom,LinearMap.id,rfl⟩

theorem evaluatedLift_ne_zero (H : ℚ) (hH : H ≠ 0) : evaluatedLift H hH ≠ 0 := by
  intro hz
  apply evaluatedLift_not_projectiveFactors H hH
  rw [hz]
  exact Submodule.zero_mem _

end
end TachikawaCharZero.FixedYEvaluation
