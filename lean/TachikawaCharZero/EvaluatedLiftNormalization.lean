import TachikawaCharZero.EvaluatedCompleteY

/-! Normalize the actual fixed-Y bimodule lifts by their evaluated rational
coordinates. This fixes degree zero; generator action and twist weights
for the all-degree branch formula are separate proof obligations. -/
namespace TachikawaCharZero.EvaluatedLiftNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open ScalingSocle SocleBimodule FixedBimoduleY ReverseCorner
open scoped TensorProduct ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def coordinate (H : ℚ) (hH : H≠0) : ℚ :=
  evaluatedWZeroEquiv (EvaluatedWProfile.wZero H hH)

theorem coordinate_ne_zero (H : ℚ) (hH : H≠0) : coordinate H hH≠0 := by
  intro hc
  apply EvaluatedWProfile.wZero_ne_zero H hH
  apply evaluatedWZeroEquiv.injective
  exact hc.trans evaluatedWZeroEquiv.map_zero.symm

def coefficient (H : ℚ) (hH : H≠0) : ℚ :=
  coordinate H hH / coordinate 2 (by norm_num)

theorem coefficient_ne_zero (H : ℚ) (hH : H≠0) : coefficient H hH≠0 :=
  div_ne_zero (coordinate_ne_zero H hH) (coordinate_ne_zero 2 (by norm_num))

theorem wZero_eq_coefficient_smul (H : ℚ) (hH : H≠0) :
    EvaluatedWProfile.wZero H hH=
      coefficient H hH • EvaluatedWProfile.wZero 2 (by norm_num) := by
  apply evaluatedWZeroEquiv.injective
  rw [map_smul]
  change coordinate H hH=(coordinate H hH / coordinate 2 (by norm_num)) *
    coordinate 2 (by norm_num)
  exact (div_mul_cancel₀ _ (coordinate_ne_zero 2 (by norm_num))).symm

def lift (H : ℚ) (hH : H≠0) : (TwistedSocleLifts.finiteU H hH).obj ⟶ Y.obj :=
  (coefficient H hH)⁻¹ • FixedYLifts.lift H hH

def evaluatedLift (H : ℚ) (hH : H≠0) : X ⟶ Enveloping.evalObj X Y.obj :=
  (FixedYEvaluation.uXIso H hH).inv ≫ Enveloping.evalMap X (lift H hH)

theorem evalMap_smul {M N : ModuleCat EE} (c : ℚ) (f : M ⟶ N) :
    Enveloping.evalMap X (c • f)=c • Enveloping.evalMap X f := by
  exact (Enveloping.evaluation (k:=ℚ) (S:=E) X).map_smul c f

theorem evaluatedLift_eq_smul (H : ℚ) (hH : H≠0) :
    evaluatedLift H hH=(coefficient H hH)⁻¹ • FixedYEvaluation.evaluatedLift H hH := by
  unfold evaluatedLift lift FixedYEvaluation.evaluatedLift
  rw [evalMap_smul,CategoryTheory.Linear.comp_smul]

theorem normalized_stable_class (H : ℚ) (hH : H≠0) :
    stableClass (k:=ℚ) (evaluatedLift H hH).hom=
      EvaluatedWProfile.wZero 2 (by norm_num) := by
  rw [evaluatedLift_eq_smul]
  change stableClass (k:=ℚ) ((coefficient H hH)⁻¹ •
    (FixedYEvaluation.evaluatedLift H hH).hom)=_
  rw [map_smul]
  change (coefficient H hH)⁻¹ • EvaluatedWProfile.wZero H hH=_
  rw [wZero_eq_coefficient_smul,smul_smul,inv_mul_cancel₀ (coefficient_ne_zero H hH),one_smul]

theorem normalized_two_branches :
    stableClass (k:=ℚ) (evaluatedLift 2 (by norm_num)).hom=
      stableClass (k:=ℚ) (evaluatedLift 3 (by norm_num)).hom :=
  (normalized_stable_class 2 (by norm_num)).trans
    (normalized_stable_class 3 (by norm_num)).symm

theorem evaluatedLift_stable_ne_zero (H : ℚ) (hH : H≠0) :
    stableClass (k:=ℚ) (evaluatedLift H hH).hom≠0 := by
  rw [normalized_stable_class]
  exact EvaluatedWProfile.wZero_ne_zero 2 (by norm_num)

end
end TachikawaCharZero.EvaluatedLiftNormalization
