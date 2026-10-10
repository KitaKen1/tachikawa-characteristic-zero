import TachikawaCharZero.FixedYEvaluation
import OAI.RingTheory.Tachikawa.EvaluationCokernels

/-! Evaluation of the actual chosen signed source and its cokernels.
The finite evaluated degree-five cokernel is fixed before any profile claim.
No comparison with the signed Koszul fiber is assumed. -/
namespace TachikawaCharZero.EvaluatedSource
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

section Generic
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def finiteEval (X : ModuleCat R) [FiniteDimensional k X]
    (M : FiniteModule k (Enveloping.Alg k S R)) : FiniteModule k S :=
  ⟨Enveloping.evalObj X M.obj,inferInstance⟩

end Generic

open ScalingSocle SocleBimodule FixedBimoduleY InducedTwistedSocle
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

abbrev sourceChain := reflectCochain inducedComplex
abbrev evaluationFunctor := Enveloping.evaluation (k := ℚ) (S := E) X
abbrev evaluatedChain := (evaluationFunctor.mapHomologicalComplex (.down ℤ)).obj sourceChain

theorem source_term_finite (j : ℤ) : Module.Finite EE (sourceChain.X j) :=
  induced_term_finite (-j)

theorem source_term_projective (j : ℤ) : Module.Projective EE (sourceChain.X j) :=
  induced_term_projective (-j)

theorem evaluated_term_finite (j : ℤ) : Module.Finite E (evaluatedChain.X j) := by
  let : Module.Finite EE (sourceChain.X j) := source_term_finite j
  let : FiniteDimensional ℚ (sourceChain.X j) := Module.Finite.trans EE (sourceChain.X j)
  change Module.Finite E (Enveloping.evalObj X (sourceChain.X j))
  infer_instance

theorem evaluated_term_projective (j : ℤ) : Module.Projective E (evaluatedChain.X j) := by
  let : Module.Projective EE (sourceChain.X j) := source_term_projective j
  change Module.Projective E (Enveloping.evalObj X (sourceChain.X j))
  infer_instance

def sourceCokerIso (j : ℤ) :
    Enveloping.evalObj X (TwistedStableGate.sourceCoker j).obj ≅
      ModuleCat.of E (CokerAt evaluatedChain j) :=
  Enveloping.evalCokerIso X (sourceChain.d (j+1) j)

def N_X : FiniteModule ℚ E := finiteEval X N

def N_X_cokerIso : N_X.obj ≅ ModuleCat.of E (CokerAt evaluatedChain 5) :=
  sourceCokerIso 5

end
end TachikawaCharZero.EvaluatedSource
