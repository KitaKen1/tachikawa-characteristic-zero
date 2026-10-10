import TachikawaCharZero.TateTwistWeights

/-! The actual projected tensor action reduces to the proved complete twist.
This connects the weights to any concrete bimodule and complete lift whose
augmentation and projection squares are supplied. Construction of the final
fiber bimodule and those squares remains a separate obligation. -/
namespace TachikawaCharZero.TwistedBranchWeights
noncomputable section
open CategoryTheory OAI.Tachikawa TensorProfile
open scoped ModuleCat.Algebra

variable (H : ℚ) (hH : H ≠ 0)

def weight : ℤ → ℚ
  | .ofNat n => (H⁻¹)^(n/3)
  | .negSucc n => H^2*H^(n/3)

theorem action_all (a : ℤ) (x : TateProfile.Tate a) :
    TateTwistWeights.action H hH a x=weight H a • x := by
  cases a with
  | ofNat n =>
    cases n with
    | zero =>
      change TateTwistWeights.action H hH 0 x = (H⁻¹)^0 • x
      simpa only [pow_zero,one_smul] using TateTwistWeights.zero H hH x
    | succ n => exact TateTwistWeights.positive H hH n x
  | negSucc n =>
    cases n with
    | zero =>
      change TateTwistWeights.action H hH (-1) x = (H^2*H^0) • x
      simpa only [pow_zero,mul_one] using TateTwistWeights.negative_one H hH x
    | succ n => exact TateTwistWeights.negative H hH n x

variable {B : ModuleCat (Enveloping.Alg ℚ E E)}
  (l : TateProfile.P ⟶ Enveloping.tensorComplex B TateProfile.P)
  (p : B ⟶ Enveloping.twistedRegular (TensorTwistWeights.scale H hH))

def projectedMap :
    completeHom (k:=ℚ) TateProfile.P X₂ ⟶ completeHom (k:=ℚ) TateProfile.P X₂ :=
  completeFunctorHom (k:=ℚ) (Enveloping.tensorFunctor B)
    TateProfile.P TateProfile.P X₂ l ≫
      completeHomMap TateProfile.P
        (Enveloping.evalMap X₂ p ≫
          (Enveloping.twistedTensorIso (TensorTwistWeights.scale H hH) X₂).hom ≫
          (TensorTwistWeights.simpleIso H hH).hom)

variable (v : X₂ ⟶ (Enveloping.tensorFunctor B).obj X₂)
  (hl : l.f 0 ≫ (Enveloping.tensorFunctor B).map
    (ModuleCat.ofHom StableSeam.finiteX.cover.map) =
      ModuleCat.ofHom StableSeam.finiteX.cover.map ≫ v)
  (hv : v ≫ Enveloping.evalMap X₂ p =
    (TensorTwistWeights.simpleIso H hH).inv ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H hH) X₂).inv)

include hl hv in
theorem projected_eq (a : ℤ) :
    VectorSplit.Hmap (projectedMap H hH l p) a = TateTwistWeights.action H hH a :=
  Enveloping.tensor_projected_action StableSeam.finiteX TateProfile.form
    (TensorTwistWeights.scale H hH) (TensorTwistWeights.simpleIso H hH)
    v l hl p hv a

include hl hv in
theorem projected_weight (a : ℤ) (x : TateProfile.Tate a) :
    VectorSplit.Hmap (projectedMap H hH l p) a x = weight H a • x := by
  rw [projected_eq H hH l p v hl hv]
  exact action_all H hH a x

end
end TachikawaCharZero.TwistedBranchWeights
