import TachikawaCharZero.InducedHighExactness
import TachikawaCharZero.TwistSideRestriction
import TachikawaCharZero.RestrictedPerfect
import OAI.RingTheory.Tachikawa.InductionRightComparison
import OAI.RingTheory.Tachikawa.CokerComparison

/-! The actual chosen signed source cokernels in reflected degrees at least
five are projective after forgetting either enveloping action. The proof
transports the existing length-four side resolutions through actual
homotopies and the identity-based twist/forgetful comparisons. -/
namespace TachikawaCharZero.SourceSideProjectivity
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open ScalingSocle InducedTwistedSocle SignedSourceComparison
open scoped TensorProduct ModuleCat.Algebra
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

abbrev chain := (inductionFunctor.mapHomologicalComplex (.down ℕ)).obj resolution.complex
abbrev leftForget := Enveloping.leftFunctor (k := ℚ) (R := E) (S := E)
abbrev rightForget := Enveloping.rightFunctor (k := ℚ) (R := E) (S := E)
abbrev rightTwist := TwistSideRestriction.rightRestriction SignedTrivialAutomorphism.signedE
abbrev rightSideInduction := AlgebraInduction.functor (k := ℚ)
  (R := ScalingSocle.Bᵐᵒᵖ) (S := Eᵐᵒᵖ) inclusionB.op
abbrev leftBounded := (InducedHighExactness.sideInduction.mapHomologicalComplex (.down ℕ)).obj
  RestrictionDimension.leftEResolution.complex
abbrev rightBounded := (rightTwist.mapHomologicalComplex (.down ℕ)).obj
  ((rightSideInduction.mapHomologicalComplex (.down ℕ)).obj
    RestrictedPerfect.rightEResolution.complex)

def untwistedRightHomotopy := Enveloping.inducedRightHomotopy (k := ℚ)
  (R := ScalingSocle.B) (S := E) inclusionB RestrictedPerfect.rightEResolution

def signedLeftHomotopy : HomotopyEquiv (Enveloping.leftComplex chain) leftBounded :=
  (leftForget.mapHomotopyEquiv inducedHomotopy).trans
    ((HomotopyEquiv.ofIso
      ((NatIso.mapHomologicalComplex
        (TwistSideRestriction.leftComparison SignedTrivialAutomorphism.signedE) (.down ℕ)).app
          untwistedChain)).trans InducedHighExactness.untwistedLeftHomotopy)

def signedRightHomotopy : HomotopyEquiv (Enveloping.rightComplex chain) rightBounded :=
  (rightForget.mapHomotopyEquiv inducedHomotopy).trans
    ((HomotopyEquiv.ofIso
      ((NatIso.mapHomologicalComplex
        (TwistSideRestriction.rightComparison SignedTrivialAutomorphism.signedE) (.down ℕ)).app
          untwistedChain)).trans (rightTwist.mapHomotopyEquiv untwistedRightHomotopy))

theorem chain_term_projective (n : ℕ) : Module.Projective EE (chain.X n) := by
  let e := inductionFunctor.mapIso (resolution.cochainComplexXIso (-(n : ℤ)) n rfl)
  let : Module.Projective EE
      (inductionFunctor.obj (resolution.cochainComplex.X (-(n : ℤ)))) :=
    induced_term_projective (-(n : ℤ))
  exact Module.Projective.of_equiv e.toLinearEquiv

theorem chain_term_finite (n : ℕ) : Module.Finite EE (chain.X n) := by
  let e := inductionFunctor.mapIso (resolution.cochainComplexXIso (-(n : ℤ)) n rfl)
  let : Module.Finite EE
      (inductionFunctor.obj (resolution.cochainComplex.X (-(n : ℤ)))) :=
    induced_term_finite (-(n : ℤ))
  exact Module.Finite.equiv e.toLinearEquiv

theorem chain_left_term_projective (n : ℕ) : Module.Projective E (Enveloping.Obj (chain.X n)) := by
  let : Module.Projective (Enveloping.Alg ℚ E E) (chain.X n) := chain_term_projective n
  let : Module.Finite (Enveloping.Alg ℚ E E) (chain.X n) := chain_term_finite n
  exact Enveloping.projective_left (chain.X n)

theorem chain_right_term_projective (n : ℕ) :
    Module.Projective Eᵐᵒᵖ (Enveloping.Obj (chain.X n)) := by
  let : Module.Projective (Enveloping.Alg ℚ E E) (chain.X n) := chain_term_projective n
  let : Module.Finite (Enveloping.Alg ℚ E E) (chain.X n) := chain_term_finite n
  exact Enveloping.projective_right (chain.X n)

theorem natCoker_left_projective (n : ℕ) (hn : 4 ≤ n) :
    Module.Projective E (Enveloping.Obj (ModuleCat.of EE (NatCoker.C chain n))) := by
  have hz : IsZero (leftBounded.X (n+1)) := InducedHighExactness.sideInduction.map_isZero
    (RestrictionDimension.leftE_above (n+1) (by omega))
  let : Subsingleton (leftBounded.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hz
  let := chain_left_term_projective n
  exact Enveloping.coker_left_projective_of_homotopy chain leftBounded n signedLeftHomotopy

theorem natCoker_right_projective (n : ℕ) (hn : 4 ≤ n) :
    Module.Projective Eᵐᵒᵖ (Enveloping.Obj (ModuleCat.of EE (NatCoker.C chain n))) := by
  have hz : IsZero (rightBounded.X (n+1)) := rightTwist.map_isZero
    (rightSideInduction.map_isZero (RestrictedPerfect.rightE_above (n+1) (by omega)))
  let : Subsingleton (rightBounded.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hz
  let := chain_right_term_projective n
  exact Enveloping.coker_right_projective_of_homotopy chain rightBounded n signedRightHomotopy

def reflectedCokerIso (n : ℕ) : (TwistedStableGate.sourceCoker (n+1 : ℕ)).obj ≅
    ModuleCat.of EE (NatCoker.C chain n) :=
  (resolutionReflectCokerEquiv resolution inductionFunctor (n+1)).toModuleIso

theorem reflectedCoker_left_projective (n : ℕ) (hn : 4 ≤ n) :
    Module.Projective E (Enveloping.Obj (TwistedStableGate.sourceCoker (n+1 : ℕ)).obj) := by
  let : Module.Projective E (leftForget.obj (ModuleCat.of EE (NatCoker.C chain n))) :=
    natCoker_left_projective n hn
  exact Module.Projective.of_equiv (leftForget.mapIso (reflectedCokerIso n)).toLinearEquiv.symm

theorem reflectedCoker_right_projective (n : ℕ) (hn : 4 ≤ n) :
    Module.Projective Eᵐᵒᵖ (Enveloping.Obj (TwistedStableGate.sourceCoker (n+1 : ℕ)).obj) := by
  let : Module.Projective Eᵐᵒᵖ (rightForget.obj (ModuleCat.of EE (NatCoker.C chain n))) :=
    natCoker_right_projective n hn
  exact Module.Projective.of_equiv (rightForget.mapIso (reflectedCokerIso n)).toLinearEquiv.symm

end
end TachikawaCharZero.SourceSideProjectivity
