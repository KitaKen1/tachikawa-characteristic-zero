import TachikawaCharZero.EvaluatedInduction
import TachikawaCharZero.NatCokerStable
import TachikawaCharZero.EvaluatedCosyzygy
import OAI.RingTheory.Tachikawa.CokerComparison

/-! The actual finite N_X is stably equivalent to the degree-five cokernel
of induction of the checked signed tensor resolution. This comparison
needs finite projective adjacent terms, not exactness of tensor induction.
The complete signed Koszul fiber is a later comparison target. -/
namespace TachikawaCharZero.EvaluatedCokerComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

section Generic
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def negativeComparison (t : SymmetrizingForm (k := k) (R := R))
    (M N : FiniteModule k R) (e : StableEquiv (k := k) M.obj N.obj) (n : ℕ) :
    StableEquiv (k := k) (M.negative t n).obj (N.negative t n).obj := by
  let P := N.complete t
  let root : StableEquiv (k := k) N.obj (ModuleCat.of R (CokerAt P 0)) :=
    StableEquiv.ofLinearEquiv (N.cokerEquiv t).symm
  let a := negativeCokerStableEquiv t P (N.complete_totallyAcyclic t).1
    (N.complete_finite t) (N.complete_projective t) M 0 (e.trans root) n
  let b := negativeCokerStableEquiv t P (N.complete_totallyAcyclic t).1
    (N.complete_finite t) (N.complete_projective t) N 0 root n
  exact a.trans b.symm

end Generic

open ScalingSocle SocleBimodule EvaluatedInduction
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

abbrev chosenEvaluatedChain :=
  (EvaluatedSource.evaluationFunctor.mapHomologicalComplex (.down ℕ)).obj chosenInducedChain

theorem chosen_term_finite (n : ℕ) : Module.Finite E (chosenEvaluatedChain.X n) := by
  let : Module.Finite EE (chosenInducedChain.X n) := SourceSideProjectivity.chain_term_finite n
  let : FiniteDimensional ℚ (chosenInducedChain.X n) :=
    Module.Finite.trans EE (chosenInducedChain.X n)
  change Module.Finite E (Enveloping.evalObj X (chosenInducedChain.X n))
  infer_instance

theorem chosen_term_projective (n : ℕ) :
    Module.Projective E (chosenEvaluatedChain.X n) := by
  let : Module.Projective EE (chosenInducedChain.X n) :=
    SourceSideProjectivity.chain_term_projective n
  change Module.Projective E (Enveloping.evalObj X (chosenInducedChain.X n))
  infer_instance

theorem tensor_resolution_term_finite (n : ℕ) :
    Module.Finite ScalingSocle.B (tensorResolution.complex.X n) := by
  apply RestrictedPerfect.total_finite
  all_goals
    intro j
    let : Module.Finite A (Resolution.projectiveResolution.complex.X j) :=
      simple_resolution_term_finite j
    exact Module.Finite.trans A (Resolution.projectiveResolution.complex.X j)

theorem induced_term_finite (n : ℕ) : Module.Finite E (inducedSimpleChain.X n) := by
  let : Module.Finite ScalingSocle.B (tensorResolution.complex.X n) :=
    tensor_resolution_term_finite n
  let : FiniteDimensional ℚ (tensorResolution.complex.X n) :=
    Module.Finite.trans ScalingSocle.B (tensorResolution.complex.X n)
  change Module.Finite E ((AlgebraInduction.functor inclusionB).obj
    (tensorResolution.complex.X n))
  let : FiniteDimensional ℚ ((AlgebraInduction.functor inclusionB).obj
      (tensorResolution.complex.X n)) := inferInstance
  exact Module.Finite.of_restrictScalars_finite ℚ E
    ((AlgebraInduction.functor inclusionB).obj (tensorResolution.complex.X n))

theorem induced_term_projective (n : ℕ) : Module.Projective E (inducedSimpleChain.X n) := by
  let : Module.Finite ScalingSocle.B (tensorResolution.complex.X n) :=
    tensor_resolution_term_finite n
  let : Projective (tensorResolution.complex.X n) := tensorResolution.projective n
  let : Module.Projective ScalingSocle.B (tensorResolution.complex.X n) :=
    ModuleCat.projective_of_module_projective (tensorResolution.complex.X n)
  change Module.Projective E ((AlgebraInduction.functor inclusionB).obj
    (tensorResolution.complex.X n))
  infer_instance

def chosenCokerIso (n : ℕ) :
    Enveloping.evalObj X (TwistedStableGate.sourceCoker n).obj ≅
      ModuleCat.of E (chosenEvaluatedChain.X n ⧸
        LinearMap.range (chosenEvaluatedChain.d (n+1) n).hom) :=
  EvaluatedSource.sourceCokerIso n ≪≫
    (resolutionReflectCokerEquiv InducedTwistedSocle.resolution
      (InducedTwistedSocle.inductionFunctor ⋙ EvaluatedSource.evaluationFunctor) n).toModuleIso

def inducedCoker : FiniteModule ℚ E where
  obj := ModuleCat.of E (NatCoker.C inducedSimpleChain 4)
  finite := by
    let : Module.Finite E (inducedSimpleChain.X (4+1)) := induced_term_finite (4+1)
    exact Module.Finite.quotient E (LinearMap.range (inducedSimpleChain.d (4+2) (4+1)).hom)

def degreeFiveComparison : StableEquiv (k := ℚ) EvaluatedSource.N_X.obj inducedCoker.obj :=
  (StableEquiv.ofLinearEquiv (chosenCokerIso 5).toLinearEquiv).trans
    (NatCokerStable.comparison signedComparison 4
      (chosen_term_finite 4) (chosen_term_projective 4)
      (induced_term_finite 4) (induced_term_projective 4))

def inducedYModel : FiniteModule ℚ E := inducedCoker.negative Starting.E_form 4

def fixedYComparison : StableEquiv (k := ℚ)
    (Enveloping.evalObj X FixedBimoduleY.Y.obj) inducedYModel.obj :=
  EvaluatedCosyzygy.fixedYComparison.trans
    (negativeComparison Starting.E_form EvaluatedSource.N_X inducedCoker
      degreeFiveComparison 4)

def modelLift (H : ℚ) (hH : H ≠ 0) : X ⟶ inducedYModel.obj :=
  ModuleCat.ofHom (fixedYComparison.hom.comp (FixedYEvaluation.evaluatedLift H hH).hom)

theorem modelLift_stable_ne_zero (H : ℚ) (hH : H ≠ 0) :
    stableClass (k := ℚ) (modelLift H hH).hom ≠ 0 := by
  intro hz
  apply FixedYEvaluation.evaluatedLift_stable_ne_zero H hH
  apply (fixedYComparison.post X).injective
  change stableClass (k := ℚ) (modelLift H hH).hom = _
  simpa only [map_zero] using hz

theorem model_nonprojective : ¬ Module.Projective E inducedYModel.obj := by
  intro hp
  apply modelLift_stable_ne_zero 2 (by norm_num)
  apply (stableClass_eq_zero_iff _).mpr
  exact ⟨inducedYModel.obj,inducedYModel.finite,hp,
    (modelLift 2 (by norm_num)).hom,LinearMap.id,rfl⟩

end
end TachikawaCharZero.EvaluatedCokerComparison
