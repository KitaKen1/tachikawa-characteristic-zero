import TachikawaCharZero.EvaluatedLiftNormalization
import TachikawaCharZero.CompleteHomNaturality

/-! The actual normalized evaluated lifts induce the same map on complete
Hom in every integer degree. Their map is an isomorphism in degree zero
and zero in all other degrees. This is postcomposition after evaluation;
the twisted bimodule branch action remains a separate obligation. -/
namespace TachikawaCharZero.EvaluatedCompleteLiftMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open ScalingSocle SocleBimodule ReverseCorner EvaluatedLiftNormalization
open scoped ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing
local notation "E" => TensorProfile.E
local instance : Module E X := inferInstanceAs (Module TensorProfile.E X)
local instance : IsScalarTower ℚ E X :=
  inferInstanceAs (IsScalarTower ℚ TensorProfile.E X)

abbrev inducedMap (H : ℚ) (hH : H≠0) (a : ℤ) :
    TateProfile.Tate a →ₗ[ℚ] VectorSplit.H completeY a :=
  completeHmap (k:=ℚ) TateProfile.P (evaluatedLift H hH) a

def zeroStableEquiv : VectorSplit.H completeY 0 ≃ₗ[ℚ] EvaluatedWProfile.W 0 :=
  CompleteHomNaturality.zeroEquiv TateProfile.P
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
    (StableSeam.finiteX.cokerEquiv TateProfile.form) EvaluatedWProfile.finiteYX.obj

theorem inducedMap_eq_reference (H : ℚ) (hH : H≠0) (a : ℤ) :
    inducedMap H hH a = inducedMap 2 (by norm_num) a := by
  apply CompleteHomNaturality.completeHmap_eq_of_stable_class TateProfile.P
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
  exact (normalized_stable_class H hH).trans
    (normalized_stable_class 2 (by norm_num)).symm

theorem stable_end_coordinate (x : StableHom (k:=ℚ) (R:=TensorProfile.E)
    (M:=TensorProfile.X₂) (N:=TensorProfile.X₂)) :
    x=StableEnd.equiv x • stableClass (k:=ℚ)
      (LinearMap.id (R:=TensorProfile.E) (M:=TensorProfile.X₂)) := by
  apply StableEnd.equiv.injective
  rw [map_smul,StableEnd.identity_coordinate,smul_eq_mul,mul_one]

theorem inducedMap_zero_formula (H : ℚ) (hH : H≠0) (x : TateProfile.Tate 0) :
    zeroStableEquiv (inducedMap H hH 0 x)=
      TateProfile.zeroEquiv x • EvaluatedWProfile.wZero 2 (by norm_num) := by
  rw [show zeroStableEquiv (inducedMap H hH 0 x)=
    stablePostcompose (evaluatedLift H hH).hom
      (CompleteHomNaturality.zeroEquiv TateProfile.P
        (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
        (StableSeam.finiteX.complete_finite TateProfile.form)
        (StableSeam.finiteX.complete_projective TateProfile.form)
        (StableSeam.finiteX.cokerEquiv TateProfile.form) X x) from
    CompleteHomNaturality.zeroEquiv_natural _ _ _ _ _ _ x]
  rw [stable_end_coordinate (CompleteHomNaturality.zeroEquiv TateProfile.P
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
    (StableSeam.finiteX.cokerEquiv TateProfile.form) X x),
    map_smul]
  change TateProfile.zeroEquiv x • stableClass (k:=ℚ) (evaluatedLift H hH).hom=
    TateProfile.zeroEquiv x • EvaluatedWProfile.wZero 2 (by norm_num)
  exact congrArg (fun z : EvaluatedWProfile.W 0 => TateProfile.zeroEquiv x • z)
    (normalized_stable_class H hH)

theorem inducedMap_zero_coordinate (H : ℚ) (hH : H≠0) (x : TateProfile.Tate 0) :
    evaluatedWZeroEquiv (zeroStableEquiv (inducedMap H hH 0 x))=
      TateProfile.zeroEquiv x * coordinate 2 (by norm_num) := by
  rw [inducedMap_zero_formula,map_smul]
  rfl

theorem inducedMap_zero_bijective (H : ℚ) (hH : H≠0) :
    Function.Bijective (inducedMap H hH 0) := by
  constructor
  · intro x y h
    apply TateProfile.zeroEquiv.injective
    have he := congrArg (fun z => evaluatedWZeroEquiv (zeroStableEquiv z)) h
    rw [inducedMap_zero_coordinate,inducedMap_zero_coordinate] at he
    exact mul_right_cancel₀ (coordinate_ne_zero 2 (by norm_num)) he
  · intro y
    let x := TateProfile.zeroEquiv.symm
      (evaluatedWZeroEquiv (zeroStableEquiv y) / coordinate 2 (by norm_num))
    refine ⟨x,?_⟩
    apply zeroStableEquiv.injective
    apply evaluatedWZeroEquiv.injective
    rw [inducedMap_zero_coordinate]
    dsimp only [x]
    rw [LinearEquiv.apply_symm_apply]
    exact div_mul_cancel₀ _ (coordinate_ne_zero 2 (by norm_num))

def zeroIso (H : ℚ) (hH : H≠0) :
    TateProfile.Tate 0 ≃ₗ[ℚ] VectorSplit.H completeY 0 :=
  LinearEquiv.ofBijective (inducedMap H hH 0) (inducedMap_zero_bijective H hH)

theorem inducedMap_off_zero (H : ℚ) (hH : H≠0) (a : ℤ) (ha : a≠0) :
    inducedMap H hH a=0 := by
  by_cases hm3 : a=-3
  · subst a
    let : Subsingleton (TateProfile.Tate (-3)) := TateProfile.negative_zero 2 (by norm_num)
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0,map_zero]
    rfl
  · let := completeYHomology_zero a hm3 ha
    exact Subsingleton.elim _ _

theorem two_branch_maps (a : ℤ) :
    inducedMap 2 (by norm_num) a=inducedMap 3 (by norm_num) a :=
  (inducedMap_eq_reference 3 (by norm_num) a).symm

end
end TachikawaCharZero.EvaluatedCompleteLiftMap
