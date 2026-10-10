import TachikawaCharZero.EvaluatedSource
import OAI.RingTheory.Tachikawa.EvaluationCosyzygy

/-! Evaluation commutes, up to actual stable equivalences, with iterated
cosyzygies of a finite right-projective bimodule. Applied to the chosen
degree-five source cokernel, this fixes an E-module model for evaluated Y. -/
namespace TachikawaCharZero.EvaluatedCosyzygy
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

section Generic
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R))
  (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat R) [FiniteDimensional k X]
  (M : FiniteModule k (Enveloping.Alg k S R))
  [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M.obj)]

theorem negative_right_projective (n : ℕ) :
    Module.Projective Rᵐᵒᵖ
      (Enveloping.Obj (M.negative (Enveloping.envelopingForm u t) n).obj) := by
  induction n with
  | zero =>
    change Module.Projective Rᵐᵒᵖ (Enveloping.Obj M.obj)
    infer_instance
  | succ n ih =>
    let := ih
    exact Enveloping.cosyzygy_right_projective u t
      (M.negative (Enveloping.envelopingForm u t) n)

def negativeCokerComparison
    (P : ChainComplex (ModuleCat S) ℤ) (hP : ComplexExact P)
    (fin : ∀ j, Module.Finite S (P.X j)) (proj : ∀ j, Module.Projective S (P.X j))
    (j : ℤ)
    (e : StableEquiv (k := k) (Enveloping.evalObj X M.obj)
      (ModuleCat.of S (CokerAt P j))) (n : ℕ) :
    StableEquiv (k := k)
      (Enveloping.evalObj X (M.negative (Enveloping.envelopingForm u t) n).obj)
      (ModuleCat.of S (CokerAt P (j-(n:ℤ)))) := by
  induction n with
  | zero =>
    change StableEquiv (k := k) (Enveloping.evalObj X M.obj)
      (ModuleCat.of S (CokerAt P (j-0)))
    rw [sub_zero]
    exact e
  | succ n ih =>
    let : Module.Projective Rᵐᵒᵖ
        (Enveloping.Obj (M.negative (Enveloping.envelopingForm u t) n).obj) :=
      negative_right_projective t u M n
    change StableEquiv (k := k)
      (Enveloping.evalObj X
        ((M.negative (Enveloping.envelopingForm u t) n).cosyzygy
          (Enveloping.envelopingForm u t)).obj) _
    rw [show j-((n+1:ℕ):ℤ) = (j-(n:ℤ))-1 by omega]
    exact Enveloping.evalCosyCokerStableEquiv t u X
      (M.negative (Enveloping.envelopingForm u t) n) P hP fin proj (j-(n:ℤ)) ih

def negativeEvaluationComparison (n : ℕ) :
    StableEquiv (k := k)
      (Enveloping.evalObj X (M.negative (Enveloping.envelopingForm u t) n).obj)
      ((EvaluatedSource.finiteEval X M).negative u n).obj := by
  let V := EvaluatedSource.finiteEval X M
  let P := V.complete u
  let e : StableEquiv (k := k) V.obj (ModuleCat.of S (CokerAt P 0)) :=
    StableEquiv.ofLinearEquiv (V.cokerEquiv u).symm
  let a := negativeCokerComparison t u X M P (V.complete_totallyAcyclic u).1
    (V.complete_finite u) (V.complete_projective u) 0 e n
  let b := negativeCokerStableEquiv u P (V.complete_totallyAcyclic u).1
    (V.complete_finite u) (V.complete_projective u) V 0 e n
  exact a.trans b.symm

end Generic

open ScalingSocle SocleBimodule FixedBimoduleY EvaluatedSource
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def YXModel : FiniteModule ℚ E := N_X.negative Starting.E_form 4

def fixedYComparison : StableEquiv (k := ℚ) (Enveloping.evalObj X Y.obj) YXModel.obj := by
  let : Module.Projective Eᵐᵒᵖ (Enveloping.Obj N.obj) := N_right_projective
  exact negativeEvaluationComparison Starting.E_form Starting.E_form X N 4

def modelLift (H : ℚ) (hH : H ≠ 0) : X ⟶ YXModel.obj :=
  ModuleCat.ofHom (fixedYComparison.hom.comp (FixedYEvaluation.evaluatedLift H hH).hom)

theorem modelLift_stable_ne_zero (H : ℚ) (hH : H ≠ 0) :
    stableClass (k := ℚ) (modelLift H hH).hom ≠ 0 := by
  intro hz
  apply FixedYEvaluation.evaluatedLift_stable_ne_zero H hH
  apply (fixedYComparison.post X).injective
  change stableClass (k := ℚ) (modelLift H hH).hom = _
  simpa only [map_zero] using hz

theorem model_nonprojective : ¬ Module.Projective E YXModel.obj := by
  intro hp
  apply modelLift_stable_ne_zero 2 (by norm_num)
  apply (stableClass_eq_zero_iff _).mpr
  exact ⟨YXModel.obj,YXModel.finite,hp,(modelLift 2 (by norm_num)).hom,LinearMap.id,rfl⟩

end
end TachikawaCharZero.EvaluatedCosyzygy
