import TachikawaCharZero.TwoBranchFiber
import TachikawaCharZero.TwistedBranchWeights

/-! The concrete two-branch fiber has a complete lift. Its projections
induce the actual complete twist weights in every integer degree. -/
namespace TachikawaCharZero.TwoBranchAction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open CategoryTheory OAI.Tachikawa
open ScalingSocle SocleBimodule TwistedSocleLifts
open scoped TensorProduct ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

section Generic
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def regularCompare (σ τ : R ≃ₐ[k] R) (h : σ=τ) :
    Enveloping.twistedRegular σ ≅ Enveloping.twistedRegular τ := by
  subst τ
  exact Iso.refl _

theorem regularCompare_hom_apply (σ τ : R ≃ₐ[k] R) (h : σ=τ)
    (x : Enveloping.twistedRegular σ) :
    (show R from (regularCompare σ τ h).hom x) = (show R from x) := by
  subst τ
  rfl

theorem regularCompare_evaluated_inv (σ τ : R ≃ₐ[k] R) (h : σ=τ)
    (X : ModuleCat R) (hfix : ∀ r : R, ∀ x : X, σ r • x = r • x)
    (e : (SymmetrizingForm.twistFunctor τ).obj X ≅ X)
    (he : ∀ x : X, (show X from e.inv x)=x) :
    (Enveloping.twistedEvalIso σ X hfix).inv ≫
        Enveloping.evalMap X (regularCompare σ τ h).hom =
      e.inv ≫ (Enveloping.twistedTensorIso τ X).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Enveloping.evalMap X (regularCompare σ τ h).hom
    (BalancedTensor.mk (show Enveloping.Obj (Enveloping.twistedRegular σ) from (1:R)) x) =
      BalancedTensor.mk
        (show Enveloping.Obj (Enveloping.twistedRegular τ) from (1:R))
        (show X from e.inv x)
  rw [he,Enveloping.evalMap_mk]
  have hm : Enveloping.leftMap (regularCompare σ τ h).hom
      (show Enveloping.Obj (Enveloping.twistedRegular σ) from (1:R)) =
      (show Enveloping.Obj (Enveloping.twistedRegular τ) from (1:R)) :=
    regularCompare_hom_apply σ τ h (1:R)
  rw [hm]

end Generic

variable (H : ℚ) (hH : H ≠ 0)

def branchIso : (finiteU H hH).obj ≅
    Enveloping.twistedRegular (TensorTwistWeights.scale H hH) :=
  regularCompare (scaling H hH) (TensorTwistWeights.scale H hH)
    (TateTwistWeights.scale_eq_socle H hH).symm

theorem evaluated_branchIso : (FixedYEvaluation.uXIso H hH).inv ≫
    Enveloping.evalMap X (branchIso H hH).hom =
    (TensorTwistWeights.simpleIso H hH).inv ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H hH) X).inv := by
  exact regularCompare_evaluated_inv (scaling H hH) (TensorTwistWeights.scale H hH)
    (TateTwistWeights.scale_eq_socle H hH).symm X
    (FixedYEvaluation.scaling_fixed_X H hH) (TensorTwistWeights.simpleIso H hH)
    (fun _ => rfl)

variable (H₁ H₂ : ℚ) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

local instance leftProjective : Module.Projective E
    (Enveloping.Obj (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj) :=
  (TwoBranchFiber.side_projective H₁ H₂ h₁ h₂).1
local instance rightProjective : Module.Projective Eᵐᵒᵖ
    (Enveloping.Obj (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj) :=
  (TwoBranchFiber.side_projective H₁ H₂ h₁ h₂).2
local instance finiteGround : FiniteDimensional ℚ
    (Enveloping.Obj (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj) := by
  change Module.Finite ℚ (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj
  infer_instance

def completeLift : TateProfile.P ⟶ Enveloping.tensorComplex
    (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj TateProfile.P :=
  @Enveloping.tensorCompleteLift ℚ E _ _ _ _ (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj
    (finiteGround H₁ H₂ h₁ h₂) (TwoBranchFiber.side_projective H₁ H₂ h₁ h₂).1
    (TwoBranchFiber.side_projective H₁ H₂ h₁ h₂).2
    StableSeam.finiteX TateProfile.form (TwoBranchFiber.vZero H₁ H₂ h₁ h₂)

theorem completeLift_aug : (completeLift H₁ H₂ h₁ h₂).f 0 ≫
    (Enveloping.tensorFunctor (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj).map
      (ModuleCat.ofHom StableSeam.finiteX.cover.map) =
    ModuleCat.ofHom StableSeam.finiteX.cover.map ≫ TwoBranchFiber.vZero H₁ H₂ h₁ h₂ :=
  @Enveloping.tensorCompleteLift_aug ℚ E _ _ _ _ (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj
    (finiteGround H₁ H₂ h₁ h₂) (TwoBranchFiber.side_projective H₁ H₂ h₁ h₂).1
    (TwoBranchFiber.side_projective H₁ H₂ h₁ h₂).2
    StableSeam.finiteX TateProfile.form (TwoBranchFiber.vZero H₁ H₂ h₁ h₂)

def first : (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj ⟶
    Enveloping.twistedRegular (TensorTwistWeights.scale H₁ h₁) :=
  TwoBranchFiber.first H₁ H₂ h₁ h₂ ≫ (branchIso H₁ h₁).hom
def second : (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj ⟶
    Enveloping.twistedRegular (TensorTwistWeights.scale H₂ h₂) :=
  TwoBranchFiber.second H₁ H₂ h₁ h₂ ≫ (branchIso H₂ h₂).hom

theorem vZero_first : TwoBranchFiber.vZero H₁ H₂ h₁ h₂ ≫
    Enveloping.evalMap X (first H₁ H₂ h₁ h₂) =
    (TensorTwistWeights.simpleIso H₁ h₁).inv ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₁ h₁) X).inv := by
  change _ ≫ (Enveloping.evaluation (k:=ℚ) (S:=E) X).map (_ ≫ _) = _
  rw [CategoryTheory.Functor.map_comp,← Category.assoc]
  exact (congrArg (fun f => f ≫ Enveloping.evalMap X (branchIso H₁ h₁).hom)
    (TwoBranchFiber.vZero_first H₁ H₂ h₁ h₂)).trans (evaluated_branchIso H₁ h₁)

theorem vZero_second : TwoBranchFiber.vZero H₁ H₂ h₁ h₂ ≫
    Enveloping.evalMap X (second H₁ H₂ h₁ h₂) =
    (TensorTwistWeights.simpleIso H₂ h₂).inv ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₂ h₂) X).inv := by
  change _ ≫ (Enveloping.evaluation (k:=ℚ) (S:=E) X).map (_ ≫ _) = _
  rw [CategoryTheory.Functor.map_comp,← Category.assoc]
  exact (congrArg (fun f => f ≫ Enveloping.evalMap X (branchIso H₂ h₂).hom)
    (TwoBranchFiber.vZero_second H₁ H₂ h₁ h₂)).trans (evaluated_branchIso H₂ h₂)

abbrev firstMap := TwistedBranchWeights.projectedMap H₁ h₁
  (completeLift H₁ H₂ h₁ h₂) (first H₁ H₂ h₁ h₂)
abbrev secondMap := TwistedBranchWeights.projectedMap H₂ h₂
  (completeLift H₁ H₂ h₁ h₂) (second H₁ H₂ h₁ h₂)

theorem first_weight (a : ℤ) (x : TateProfile.Tate a) :
    VectorSplit.Hmap (firstMap H₁ H₂ h₁ h₂) a x =
      TwistedBranchWeights.weight H₁ a • x :=
  TwistedBranchWeights.projected_weight H₁ h₁ _ _
    (TwoBranchFiber.vZero H₁ H₂ h₁ h₂) (completeLift_aug H₁ H₂ h₁ h₂)
    (vZero_first H₁ H₂ h₁ h₂) a x

theorem second_weight (a : ℤ) (x : TateProfile.Tate a) :
    VectorSplit.Hmap (secondMap H₁ H₂ h₁ h₂) a x =
      TwistedBranchWeights.weight H₂ a • x :=
  TwistedBranchWeights.projected_weight H₂ h₂ _ _
    (TwoBranchFiber.vZero H₁ H₂ h₁ h₂) (completeLift_aug H₁ H₂ h₁ h₂)
    (vZero_second H₁ H₂ h₁ h₂) a x

end
end TachikawaCharZero.TwoBranchAction
