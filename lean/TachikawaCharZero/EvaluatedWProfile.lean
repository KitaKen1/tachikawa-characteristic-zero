import TachikawaCharZero.EvaluatedCosyzygy

/-! Actual all-integer stable Hom spaces for evaluated Y, with a detected
nonzero degree-zero class. Finiteness and a rational line in degree zero
are proved. The one-dimensional {-3,0} support profile is not inferred. -/
namespace TachikawaCharZero.EvaluatedWProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open ScalingSocle SocleBimodule FixedBimoduleY
open scoped ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def finiteYX : FiniteModule ℚ E := EvaluatedSource.finiteEval X Y

def shift (M : FiniteModule ℚ E) : ℤ → FiniteModule ℚ E
  | .ofNat n => M.negative Starting.E_form n
  | .negSucc n => M.positive (n+1)

abbrev W (a : ℤ) := StableHom (k := ℚ) (R := E)
  (M := X) (N := (shift finiteYX a).obj)

theorem W_finite (a : ℤ) : Module.Finite ℚ (W a) := by
  let V := shift finiteYX a
  let : Module.Finite E V.obj := V.finite
  let : FiniteDimensional ℚ V.obj := Module.Finite.trans E V.obj
  change Module.Finite ℚ ((X →ₗ[E] V.obj) ⧸ projectiveFactors (k := ℚ))
  infer_instance

def wZero (H : ℚ) (hH : H ≠ 0) : W 0 :=
  stableClass (k := ℚ) (FixedYEvaluation.evaluatedLift H hH).hom

theorem wZero_ne_zero (H : ℚ) (hH : H ≠ 0) : wZero H hH ≠ 0 :=
  FixedYEvaluation.evaluatedLift_stable_ne_zero H hH

theorem W_zero_nontrivial : Nontrivial (W 0) :=
  ⟨⟨wZero 2 (by norm_num),0,wZero_ne_zero 2 (by norm_num)⟩⟩

def rationalLine : ℚ →ₗ[ℚ] W 0 :=
  (LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (wZero 2 (by norm_num))

theorem rationalLine_injective : Function.Injective rationalLine := by
  intro a b h
  change a • wZero 2 (by norm_num) = b • wZero 2 (by norm_num) at h
  have hz : (a-b) • wZero 2 (by norm_num) = 0 := by
    rw [sub_smul,h,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right
    (wZero_ne_zero 2 (by norm_num)))

end
end TachikawaCharZero.EvaluatedWProfile
