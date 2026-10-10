import TachikawaCharZero.FiberExceptionalProfile
import TachikawaCharZero.TateProfile

/-! The actual complete-Hom profile from X to evaluated Y in all integers.
Translation of two complete cokernels is characteristic-independent;
this specialization follows pinned OpenAI Math HomProfile.lean, 949--994
(Apache-2.0), using the signed rational tensor fiber. -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
set_option backward.isDefEq.respectTransparency false
open TachikawaCharZero.Starting OAI.Tachikawa CategoryTheory
open scoped ModuleCat.Algebra
local instance : Module E SocleBimodule.X :=
  inferInstanceAs (Module TensorProfile.E SocleBimodule.X)
local instance : IsScalarTower ℚ E SocleBimodule.X :=
  inferInstanceAs (IsScalarTower ℚ TensorProfile.E SocleBimodule.X)

abbrev completeY := completeHom (k:=ℚ) TateProfile.P EvaluatedWProfile.finiteYX.obj

def completeYStableEquiv (a : ℤ) : StableMap (k:=ℚ)
    (ModuleCat.of E (CokerAt TateProfile.P a)) EvaluatedWProfile.finiteYX.obj ≃ₗ[ℚ]
    EvaluatedWProfile.W a := by
  let : Module.Injective E E := E_injective
  let : Module.Injective TensorProfile.E TensorProfile.E := TateProfile.form.injective
  let e₁ := evaluatedFiberComparison.post (ModuleCat.of E (CokerAt TateProfile.P a))
  have e₂ := cokerStableHomTranslate TateProfile.P
    (StableSeam.finiteX.complete_exact TateProfile.form) tensorFiber tensorFiber_exact
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
    tensorFiber_term_finite tensorFiber_term_projective 0 (1-a) a (k:=ℚ)
  rw [zero_add,show 1-a+a=1 by omega] at e₂
  let e₃ := (StableEquiv.ofLinearEquiv (k:=ℚ)
    (M:=ModuleCat.of E (CokerAt TateProfile.P 0)) (N:=SocleBimodule.X)
    (StableSeam.finiteX.cokerEquiv TateProfile.form)).pre
      (ModuleCat.of E (CokerAt tensorFiber (1-a)))
  let e₄ := (evaluatedShiftFiberComparison a).post SocleBimodule.X
  exact e₁.trans (e₂.symm.trans (e₃.trans e₄.symm))

def completeYHomologyEquiv (a : ℤ) : VectorSplit.H completeY a ≃ₗ[ℚ]
    EvaluatedWProfile.W a :=
  (CompleteHom.equiv TateProfile.P EvaluatedWProfile.finiteYX.obj
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form) a).trans
      (completeYStableEquiv a)

def completeYZeroEquiv : VectorSplit.H completeY 0 ≃ₗ[ℚ] ℚ :=
  (completeYHomologyEquiv 0).trans evaluatedWZeroEquiv

def completeYMinusThreeEquiv : VectorSplit.H completeY (-3) ≃ₗ[ℚ] ℚ :=
  (completeYHomologyEquiv (-3)).trans evaluatedWMinusThreeEquiv

theorem completeYHomology_zero (a : ℤ) (hm3 : a≠-3) (h0 : a≠0) :
    Subsingleton (VectorSplit.H completeY a) := by
  let := evaluatedW_subsingleton a h0 hm3
  exact (completeYHomologyEquiv a).injective.subsingleton

theorem completeYHomology_finrank (a : ℤ) : Module.finrank ℚ (VectorSplit.H completeY a)=
    if a=-3 ∨ a=0 then 1 else 0 := by
  rw [(completeYHomologyEquiv a).finrank_eq]
  exact evaluatedW_finrank a

end
end TachikawaCharZero.ReverseCorner
