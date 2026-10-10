import TachikawaCharZero.SignedFiberHom
import TachikawaCharZero.PeriodicExt
import OAI.RingTheory.Tachikawa.SupportedTensorHom
import OAI.RingTheory.Tachikawa.IsolatedStableCoker

/-! Exceptional rational lines of the actual evaluated W profile.
The support and isolated-cokernel arguments use characteristic-independent
excerpts from pinned OpenAI Math HomProfile.lean (Apache-2.0). -/
namespace TachikawaCharZero.Induced
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Resolution CategoryTheory
open scoped ModuleCat.Algebra
local instance simpleGround : Module ℚ X := ModuleCat.Algebra.instModuleCarrier

def fGenerator : TF := ⟨TrivSqZeroExt.inl vertexF, by
  change (TrivSqZeroExt.inl vertexF:T)*TrivSqZeroExt.inl vertexF=TrivSqZeroExt.inl vertexF
  rw [TrivSqZeroExt.inl_mul_inl,vertexF_idempotent]⟩

theorem aug_fGenerator : aug fGenerator=(show S from (1:ℚ)) := rfl

theorem fGenerator_generates (a : TF) : (a:T) • fGenerator=a :=
  Subtype.ext a.property

def tfHomEquiv : (ModuleCat.of T TF ⟶ X) ≃ₗ[ℚ] ℚ where
  toFun f := f fGenerator
  invFun r := r • ModuleCat.ofHom aug
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hf := f.hom.map_smul (a:T) fGenerator
    rw [fGenerator_generates] at hf
    change f a=(a:T).fst.coeff .f*(show ℚ from f fGenerator) at hf
    change characterT (algebraMap ℚ T (show ℚ from f fGenerator))*
      (a:T).fst.coeff .f=f a
    rw [AlgHom.commutes,Algebra.algebraMap_self_apply]
    exact (mul_comm _ _).trans hf.symm
  right_inv r := by
    change characterT (algebraMap ℚ T r)*1=r
    rw [AlgHom.commutes,Algebra.algebraMap_self_apply,mul_one]
  map_add' _ _ := rfl
  map_smul' r f := by
    change characterT (algebraMap ℚ T r)*(show ℚ from f fGenerator)=
      r*(show ℚ from f fGenerator)
    rw [AlgHom.commutes,Algebra.algebraMap_self_apply]

end
end TachikawaCharZero.Induced

namespace TachikawaCharZero.ReverseCorner
noncomputable section
set_option backward.isDefEq.respectTransparency false
open TachikawaCharZero.Resolution TachikawaCharZero.Starting OAI.Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
local instance : Module T Induced.X := inferInstanceAs (Module Induced.T Induced.X)
local instance simpleGround : Module ℚ Induced.X := ModuleCat.Algebra.instModuleCarrier
local instance : SMulCommClass T ℚ Induced.X :=
  inferInstanceAs (SMulCommClass Induced.T ℚ Induced.X)

local instance (j : ℤ) : Module.Finite T (inducedForward.X j) :=
  inducedForward_term_finiteT j
local instance (j : ℤ) : Module.Finite T (inducedReverse.X j) :=
  inducedReverse_term_finiteT j
local instance (j : ℤ) : Module.Projective T (inducedForward.X j) :=
  inducedForward_term_moduleProjective j
local instance (j : ℤ) : Module.Projective T (inducedReverse.X j) :=
  inducedReverse_term_moduleProjective j
local instance (j : ℤ) : FiniteDimensional ℚ (inducedForward.X j) :=
  inducedForward_term_finite j
local instance (j : ℤ) : FiniteDimensional ℚ (inducedReverse.X j) :=
  inducedReverse_term_finite j
local instance : Module E SocleBimodule.X :=
  inferInstanceAs (Module TensorProfile.E SocleBimodule.X)
local instance : IsScalarTower ℚ E SocleBimodule.X :=
  inferInstanceAs (IsScalarTower ℚ TensorProfile.E SocleBimodule.X)

def forwardZeroHomEquiv : (inducedForward.X 0 ⟶ Induced.X) ≃ₗ[ℚ] ℚ :=
  (ModuleCat.homLinearEquiv.trans
    ((natCornerTermIso 0).toLinearEquiv.congrLeft Induced.X ℚ)).trans
    (ModuleCat.homLinearEquiv.symm.trans Induced.tfHomEquiv)

def reverseTwoHomEquiv : (inducedReverse.X 2 ⟶ Induced.X) ≃ₗ[ℚ] ℚ :=
  forwardZeroHomEquiv


def forwardTensorZeroHomEquiv : (forwardTensor.X 0 ⟶ SocleBimodule.X) ≃ₗ[ℚ] ℚ := by
  let e := OuterTensor.totalHomSupported (k:=ℚ) (A:=T) (B:=T)
    inducedForward inducedForward Induced.X Induced.X 0 0
    inducedForward_term_finiteT inducedForward_term_finiteT
    inducedForward_term_moduleProjective inducedForward_term_moduleProjective
    inducedForwardHom_zero inducedForwardHom_zero
  exact e.trans ((OuterTensor.homEquiv (k:=ℚ) (A:=T) (B:=T)
    (inducedForward.X 0) Induced.X (inducedForward.X 0) Induced.X).symm.trans
    ((TensorProduct.congr forwardZeroHomEquiv forwardZeroHomEquiv).trans
      (TensorProduct.lid ℚ ℚ)))

def reverseTensorFourHomEquiv : (reverseTensor.X 4 ⟶ SocleBimodule.X) ≃ₗ[ℚ] ℚ := by
  let e := OuterTensor.totalHomSupported (k:=ℚ) (A:=T) (B:=T)
    inducedReverse inducedReverse Induced.X Induced.X 2 2
    inducedReverse_term_finiteT inducedReverse_term_finiteT
    inducedReverse_term_moduleProjective inducedReverse_term_moduleProjective
    inducedReverseHom_zero inducedReverseHom_zero
  exact e.trans ((OuterTensor.homEquiv (k:=ℚ) (A:=T) (B:=T)
    (inducedReverse.X 2) Induced.X (inducedReverse.X 2) Induced.X).symm.trans
    ((TensorProduct.congr reverseTwoHomEquiv reverseTwoHomEquiv).trans
      (TensorProduct.lid ℚ ℚ)))

def tensorFiberHomEquiv (j : ℤ) : (tensorFiber.X j ⟶ SocleBimodule.X) ≃ₗ[ℚ]
    ((reverseTensor.X (j+1) ⟶ SocleBimodule.X) ×
      (forwardTensor.X j ⟶ SocleBimodule.X)) :=
  ModuleCat.homLinearEquiv.trans ((LinearMap.coprodEquiv ℚ).symm.trans
    (LinearEquiv.prodCongr ModuleCat.homLinearEquiv.symm ModuleCat.homLinearEquiv.symm))

def tensorFiberZeroHomEquiv : (tensorFiber.X 0 ⟶ SocleBimodule.X) ≃ₗ[ℚ] ℚ := by
  let : Subsingleton (reverseTensor.X (0+1) ⟶ SocleBimodule.X) :=
    ⟨fun f g => (reverseTensorHom_zero _ (by norm_num) f).trans
      (reverseTensorHom_zero _ (by norm_num) g).symm⟩
  let : Unique (reverseTensor.X (0+1) ⟶ SocleBimodule.X) :=
    ⟨⟨0⟩,fun _ => Subsingleton.elim _ _⟩
  exact (tensorFiberHomEquiv 0).trans ((LinearEquiv.prodComm ℚ _ _).trans
    (LinearEquiv.prodUnique.trans forwardTensorZeroHomEquiv))

def tensorFiberThreeHomEquiv : (tensorFiber.X 3 ⟶ SocleBimodule.X) ≃ₗ[ℚ] ℚ := by
  let : Subsingleton (forwardTensor.X 3 ⟶ SocleBimodule.X) :=
    ⟨fun f g => (forwardTensorHom_zero _ (by norm_num) f).trans
      (forwardTensorHom_zero _ (by norm_num) g).symm⟩
  let : Unique (forwardTensor.X 3 ⟶ SocleBimodule.X) :=
    ⟨⟨0⟩,fun _ => Subsingleton.elim _ _⟩
  exact (tensorFiberHomEquiv 3).trans
    (LinearEquiv.prodUnique.trans reverseTensorFourHomEquiv)

def fiberStableZeroEquiv : StableHom (k:=ℚ) (R:=E)
    (M:=CokerAt tensorFiber 0) (N:=SocleBimodule.X) ≃ₗ[ℚ] ℚ :=
  (stableCokerIsolatedEquiv tensorFiber SocleBimodule.X tensorFiber_totallyAcyclic
    tensorFiber_term_finite tensorFiber_term_projective 0
    (tensorFiberHom_zero _ (by norm_num) (by norm_num))
    (tensorFiberHom_zero _ (by norm_num) (by norm_num))).symm.trans tensorFiberZeroHomEquiv

def fiberStableThreeEquiv : StableHom (k:=ℚ) (R:=E)
    (M:=CokerAt tensorFiber 3) (N:=SocleBimodule.X) ≃ₗ[ℚ] ℚ :=
  (stableCokerIsolatedEquiv tensorFiber SocleBimodule.X tensorFiber_totallyAcyclic
    tensorFiber_term_finite tensorFiber_term_projective 3
    (tensorFiberHom_zero _ (by norm_num) (by norm_num))
    (tensorFiberHom_zero _ (by norm_num) (by norm_num))).symm.trans tensorFiberThreeHomEquiv

def evaluatedWFiberDualEquiv (a : ℤ) : EvaluatedWProfile.W a ≃ₗ[ℚ]
    Module.Dual ℚ (StableHom (k:=ℚ) (R:=E)
      (M:=CokerAt tensorFiber (-a)) (N:=SocleBimodule.X)) := by
  let e₁ := (evaluatedShiftFiberComparison a).post SocleBimodule.X
  have e₂ := completeCokerDuality E_form tensorFiber tensorFiber_exact
    tensorFiber_term_finite tensorFiber_term_projective (-a) SocleBimodule.X
  rw [show -a+1=1-a by omega] at e₂
  exact e₁.trans e₂

def evaluatedWZeroEquiv : EvaluatedWProfile.W 0 ≃ₗ[ℚ] ℚ :=
  (evaluatedWFiberDualEquiv 0).trans
    (fiberStableZeroEquiv.symm.dualMap.trans (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ))

def evaluatedWMinusThreeEquiv : EvaluatedWProfile.W (-3) ≃ₗ[ℚ] ℚ :=
  (evaluatedWFiberDualEquiv (-3)).trans
    (fiberStableThreeEquiv.symm.dualMap.trans (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ))

theorem evaluatedW_profile (a : ℤ) :
    ((a=-3 ∨ a=0) → Nonempty (EvaluatedWProfile.W a ≃ₗ[ℚ] ℚ)) ∧
    (a≠-3 → a≠0 → Subsingleton (EvaluatedWProfile.W a)) := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨evaluatedWMinusThreeEquiv⟩
    · exact ⟨evaluatedWZeroEquiv⟩
  · intro hm3 h0
    exact evaluatedW_subsingleton a h0 hm3

theorem evaluatedW_zero_finrank : Module.finrank ℚ (EvaluatedWProfile.W 0)=1 := by
  rw [evaluatedWZeroEquiv.finrank_eq]
  exact Module.finrank_self ℚ

theorem evaluatedW_minus_three_finrank : Module.finrank ℚ (EvaluatedWProfile.W (-3))=1 := by
  rw [evaluatedWMinusThreeEquiv.finrank_eq]
  exact Module.finrank_self ℚ

theorem evaluatedW_finrank (a : ℤ) : Module.finrank ℚ (EvaluatedWProfile.W a)=
    if a=-3 ∨ a=0 then 1 else 0 := by
  split_ifs with ha
  · obtain ⟨e⟩ := (evaluatedW_profile a).1 ha
    rw [e.finrank_eq]
    exact Module.finrank_self ℚ
  · let := evaluatedW_subsingleton a (by tauto) (by tauto)
    exact Module.finrank_zero_of_subsingleton

end
end TachikawaCharZero.ReverseCorner
