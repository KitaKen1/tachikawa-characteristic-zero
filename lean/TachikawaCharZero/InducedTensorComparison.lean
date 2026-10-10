import TachikawaCharZero.EvaluatedCokerComparison
import TachikawaCharZero.InductionCorner
import OAI.RingTheory.Tachikawa.InductionTensorTotal

/-! Actual induction of the signed rational C-simple resolution is the
checked corner complex J. Consequently the evaluated chosen source is
homotopy equivalent to the signed total J tensor J. This comparison uses
principal projectives directly and keeps the total-complex signs. -/
namespace TachikawaCharZero.InducedTensorComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open ScalingSocle Resolution EvaluatedInduction

abbrev balancedInducedChain :=
  ((AlgebraInduction.functor inclusionC).mapHomologicalComplex (.down ℕ)).obj
    projectiveResolution.complex

def termIso (n : ℕ) : balancedInducedChain.X n ≅ Induced.complex.X n := by
  cases n with
  | zero => exact InductionCorner.iso inclusionC vertexF_idempotent
  | succ n => exact InductionCorner.iso inclusionC vertexE_idempotent

def cornerChainIso : balancedInducedChain ≅ Induced.complex :=
  HomologicalComplex.Hom.isoOfComponents termIso (by
    intro i j hij
    have h : j+1=i := by simpa using hij
    subst i
    rw [Functor.mapHomologicalComplex_obj_d,projectiveResolution_d]
    change _ = _ ≫ (termIso j).hom
    symm
    cases j with
    | zero =>
      exact InductionCorner.forward_mulRight inclusionC
        (OAI.ArExplicit.BaseAlgebra.basisVector 2 .u) u_fixed_by_f
    | succ j =>
      rw [show Induced.complex.d (j+1+1) (j+1) = Induced.d (j+1) from
        ChainComplex.of_d _ _ (j+1)]
      exact InductionCorner.forward_mulRight inclusionC (p := vertexE)
        (ell ((-2:ℚ)^j)) (ell_mem _))

abbrev cornerTensorChain := mapBifunctor Induced.complex Induced.complex
  (OuterTensor.bifunctor ℚ T T) (.down ℕ)

def cornerTensorIso :
    mapBifunctor balancedInducedChain balancedInducedChain
      (OuterTensor.bifunctor ℚ T T) (.down ℕ) ≅ cornerTensorChain := by
  let F := (OuterTensor.bifunctor ℚ T T).map₂HomologicalComplex
    (.down ℕ) (.down ℕ) (.down ℕ)
  exact ((F.mapIso cornerChainIso).app balancedInducedChain) ≪≫
    ((F.obj Induced.complex).mapIso cornerChainIso)

def inducedTensorIso : inducedSimpleChain ≅ cornerTensorChain :=
  OuterTensor.inductionTotalIso inclusionC inclusionC
    projectiveResolution.complex projectiveResolution.complex ≪≫ cornerTensorIso

def evaluatedTensorComparison : HomotopyEquiv
    EvaluatedCokerComparison.chosenEvaluatedChain cornerTensorChain :=
  signedComparison.trans (HomotopyEquiv.ofIso inducedTensorIso)

theorem evaluated_exactAt_iff (n : ℕ) :
    EvaluatedCokerComparison.chosenEvaluatedChain.ExactAt n ↔
      cornerTensorChain.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff_isZero_homology]
  exact (evaluatedTensorComparison.toHomologyIso n).isZero_iff

end
end TachikawaCharZero.InducedTensorComparison
