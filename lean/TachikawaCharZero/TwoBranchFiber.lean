import TachikawaCharZero.EvaluatedLiftNormalization
import TachikawaCharZero.StableFiberPair

/-! The actual finite rational two-branch fiber. The second normalized lift
is negated, retaining the characteristic-zero difference. Right splitting
makes its evaluation at X short exact. Stable equality of the two normalized
lifts then produces an actual evaluated map with both projections equal to
the identity-normalized twist inverses. The generic fiber and stable-kernel
correction are attributed pinned excerpts; the signs and specialization here
are the rational construction. -/
namespace TachikawaCharZero.TwoBranchFiber
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa
open ScalingSocle SocleBimodule FixedBimoduleY TwistedSocleLifts
open scoped ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

variable (H₁ H₂ : ℚ) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev U := finiteU H₁ h₁
abbrev V := finiteU H₂ h₂
abbrev Q := Enveloping.fiberCover Y
abbrev middle := Enveloping.fiberMiddle (U H₁ h₁) (V H₂ h₂) Y

def F : FiniteModule ℚ EE := Enveloping.fiber (U H₁ h₁) (V H₂ h₂) Y
  (EvaluatedLiftNormalization.lift H₁ h₁) (-EvaluatedLiftNormalization.lift H₂ h₂)
abbrev projection := Enveloping.fiberProjection (U H₁ h₁) (V H₂ h₂) Y
  (EvaluatedLiftNormalization.lift H₁ h₁) (-EvaluatedLiftNormalization.lift H₂ h₂)
abbrev inclusion := Enveloping.fiberInclusion (U H₁ h₁) (V H₂ h₂) Y
  (EvaluatedLiftNormalization.lift H₁ h₁) (-EvaluatedLiftNormalization.lift H₂ h₂)
abbrev first := inclusion H₁ H₂ h₁ h₂ ≫ Enveloping.fiberFst (U H₁ h₁) (V H₂ h₂) Y
abbrev second := inclusion H₁ H₂ h₁ h₂ ≫ Enveloping.fiberSnd (U H₁ h₁) (V H₂ h₂) Y

theorem projection_apply (x : middle H₁ H₂ h₁ h₂) :
    projection H₁ H₂ h₁ h₂ x = EvaluatedLiftNormalization.lift H₁ h₁ x.1 -
      EvaluatedLiftNormalization.lift H₂ h₂ x.2.1 + Y.cover.map x.2.2 := by
  change (EvaluatedLiftNormalization.lift H₁ h₁).hom x.1 +
    ((-EvaluatedLiftNormalization.lift H₂ h₂).hom x.2.1 + Y.cover.map x.2.2) = _
  rw [ModuleCat.hom_neg,LinearMap.neg_apply]
  abel

theorem projection_surjective : Function.Surjective (projection H₁ H₂ h₁ h₂) :=
  Enveloping.fiberProjection_surjective _ _ _ _ _
theorem inclusion_injective : Function.Injective (inclusion H₁ H₂ h₁ h₂) :=
  Enveloping.fiberInclusion_injective _ _ _ _ _
theorem exact : Function.Exact (inclusion H₁ H₂ h₁ h₂) (projection H₁ H₂ h₁ h₂) :=
  Enveloping.fiber_exact _ _ _ _ _

theorem side_projective :
    Module.Projective E (Enveloping.Obj (F H₁ H₂ h₁ h₂).obj) ∧
    Module.Projective Eᵐᵒᵖ (Enveloping.Obj (F H₁ H₂ h₁ h₂).obj) := by
  let : Module.Projective E (Enveloping.Obj (U H₁ h₁).obj) := by
    change Module.Projective E (Enveloping.Obj (UH H₁ h₁))
    infer_instance
  let : Module.Projective E (Enveloping.Obj (V H₂ h₂).obj) := by
    change Module.Projective E (Enveloping.Obj (UH H₂ h₂))
    infer_instance
  let := FixedYEvaluation.U_right_projective H₁ h₁
  let := FixedYEvaluation.U_right_projective H₂ h₂
  let := Y_side_projective.1
  let := Y_side_projective.2
  exact ⟨Enveloping.fiber_left_projective _ _ _ _ _,
    Enveloping.fiber_right_projective _ _ _ _ _⟩

theorem finite : Module.Finite EE (F H₁ H₂ h₁ h₂).obj := (F H₁ H₂ h₁ h₂).finite

theorem evaluated_injective : Function.Injective
    (Enveloping.evalMap X (inclusion H₁ H₂ h₁ h₂)) := by
  exact @Enveloping.evalMap_injective ℚ E E _ _ _ _ _ X
    (F H₁ H₂ h₁ h₂).obj (middle H₁ H₂ h₁ h₂) _ _
    (side_projective H₁ H₂ h₁ h₂).2 Starting.E_form (inclusion H₁ H₂ h₁ h₂)
    (inclusion_injective H₁ H₂ h₁ h₂)

theorem evaluated_exact : Function.Exact
    (Enveloping.evalMap X (inclusion H₁ H₂ h₁ h₂))
    (Enveloping.evalMap X (projection H₁ H₂ h₁ h₂)) := by
  exact @Enveloping.evalMap_exact ℚ E E _ _ _ _ _ X
    (F H₁ H₂ h₁ h₂).obj (middle H₁ H₂ h₁ h₂) Y.obj _ _
    (side_projective H₁ H₂ h₁ h₂).2 Starting.E_form
    (inclusion H₁ H₂ h₁ h₂) (projection H₁ H₂ h₁ h₂)
    (inclusion_injective H₁ H₂ h₁ h₂) (exact H₁ H₂ h₁ h₂)
    (projection_surjective H₁ H₂ h₁ h₂)

theorem evaluated_surjective : Function.Surjective
    (Enveloping.evalMap X (projection H₁ H₂ h₁ h₂)) :=
  Enveloping.evalMap_surjective X _ (projection_surjective H₁ H₂ h₁ h₂)

theorem exists_vZero : ∃ v : X ⟶ Enveloping.evalObj X (F H₁ H₂ h₁ h₂).obj,
    v ≫ Enveloping.evalMap X (first H₁ H₂ h₁ h₂) = (FixedYEvaluation.uXIso H₁ h₁).inv ∧
    v ≫ Enveloping.evalMap X (second H₁ H₂ h₁ h₂) = (FixedYEvaluation.uXIso H₂ h₂).inv := by
  apply StableFiberPair.exists_evaluated_pair X (U H₁ h₁) (V H₂ h₂) Y
    (EvaluatedLiftNormalization.lift H₁ h₁) (EvaluatedLiftNormalization.lift H₂ h₂)
    (FixedYEvaluation.uXIso H₁ h₁) (FixedYEvaluation.uXIso H₂ h₂)
    (evaluated_injective H₁ H₂ h₁ h₂) (evaluated_exact H₁ H₂ h₁ h₂)
  change stableClass (k:=ℚ) (EvaluatedLiftNormalization.evaluatedLift H₁ h₁).hom =
    stableClass (k:=ℚ) (EvaluatedLiftNormalization.evaluatedLift H₂ h₂).hom
  rw [EvaluatedLiftNormalization.normalized_stable_class,
    EvaluatedLiftNormalization.normalized_stable_class]

def vZero := (exists_vZero H₁ H₂ h₁ h₂).choose

theorem vZero_first : vZero H₁ H₂ h₁ h₂ ≫ Enveloping.evalMap X (first H₁ H₂ h₁ h₂) =
    (FixedYEvaluation.uXIso H₁ h₁).inv := (exists_vZero H₁ H₂ h₁ h₂).choose_spec.1

theorem vZero_second : vZero H₁ H₂ h₁ h₂ ≫ Enveloping.evalMap X (second H₁ H₂ h₁ h₂) =
    (FixedYEvaluation.uXIso H₂ h₂).inv := (exists_vZero H₁ H₂ h₁ h₂).choose_spec.2

abbrev actualF := F 2 3 (by norm_num) (by norm_num)
abbrev actualV := vZero 2 3 (by norm_num) (by norm_num)

end
end TachikawaCharZero.TwoBranchFiber
