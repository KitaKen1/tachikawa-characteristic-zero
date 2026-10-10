import TachikawaCharZero.TwistEvaluation
import TachikawaCharZero.TensorDualResolution
import OAI.RingTheory.Tachikawa.EvaluationInduction

/-! The untwisted induced regular bimodule resolution, evaluated at the
actual rational X, is homotopy equivalent to induction of the tensor of
the two checked signed C-simple resolutions. No flatness of C -> T or
B -> E is assumed. The signed fiber identification remains separate. -/
namespace TachikawaCharZero.EvaluatedInduction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open ScalingSocle SocleBimodule
open scoped TensorProduct ModuleCat.Algebra
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def L : ModuleCat A := ModuleCat.of A Resolution.Simple
abbrev simpleTensor := ((OuterTensor.bifunctor ℚ A A).obj L).obj L

def simpleGround : L ≃ₗ[ℚ] ℚ where
  toFun x := Resolution.simpleRationalIso (show Resolution.Simple from x)
  invFun x := (show L from Resolution.simpleRationalIso.symm x)
  left_inv := Resolution.simpleRationalIso.symm_apply_apply
  right_inv := Resolution.simpleRationalIso.apply_symm_apply
  map_add' := Resolution.simpleRationalIso.map_add
  map_smul' c x := by
    change Resolution.simpleRationalIso ((algebraMap ℚ A c) •
      (show Resolution.Simple from x)) = c • Resolution.simpleRationalIso x
    have h := Resolution.simpleCharacterIso.map_smul (algebraMap ℚ A c)
      (show Resolution.Simple from x)
    change Resolution.simpleRationalIso ((algebraMap ℚ A c) •
      (show Resolution.Simple from x)) = Resolution.character (algebraMap ℚ A c) *
        Resolution.simpleRationalIso x at h
    simpa [Resolution.character.commutes,smul_eq_mul] using h

def ground : simpleTensor ≃ₗ[ℚ] ℚ :=
  (OuterTensor.underlyingEquiv L L).trans
    ((TensorProduct.congr simpleGround simpleGround).trans
      (TensorProduct.lid ℚ ℚ))

theorem simple_ground_action (a : A) (x : Resolution.Simple) :
    Resolution.simpleRationalIso (a • x) =
      Resolution.character a * Resolution.simpleRationalIso x :=
  Resolution.simpleCharacterIso.map_smul a x

theorem ground_action (a : ScalingSocle.B) (x : simpleTensor) :
    ground (a • x) = TwistedFactorization.character a * ground x := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_smul,map_add,ha,hb,add_mul]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add,map_add,hx,hy,mul_add]
    | tmul x y =>
      change Resolution.simpleRationalIso (a • x) *
        Resolution.simpleRationalIso (b • y) =
          (Resolution.character a * Resolution.character b) *
            (Resolution.simpleRationalIso x * Resolution.simpleRationalIso y)
      rw [simple_ground_action,simple_ground_action]
      ring

def restrictedGround : (AlgebraInduction.res inclusionB).obj X ≃ₗ[ℚ] ℚ :=
  (restrictionUnderlyingEquiv inclusionB X).trans TensorProfile.groundEquiv

def restrictionEquiv : simpleTensor ≃ₗ[ScalingSocle.B]
    (AlgebraInduction.res inclusionB).obj X where
  __ := (ground.trans restrictedGround.symm).toAddEquiv
  map_smul' a x := by
    apply restrictedGround.injective
    change restrictedGround (restrictedGround.symm (ground (a • x))) = _
    rw [restrictedGround.apply_symm_apply]
    change ground (a • x) =
      TensorProfile.groundEquiv (inclusionB a •
        (show X from restrictedGround.symm (ground x)))
    rw [SocleBimodule.ground_action,character_inclusion]
    change ground (a • x) = TwistedFactorization.character a *
      restrictedGround (restrictedGround.symm (ground x))
    rw [restrictedGround.apply_symm_apply]
    exact ground_action a x

theorem simple_resolution_term_finite (n : ℕ) :
    Module.Finite A (Resolution.projectiveResolution.complex.X n) := by
  let : Module.Finite ℚ Resolution.Ce := Module.Finite.equiv Resolution.ceIso
  let : Module.Finite ℚ Resolution.Cf := Module.Finite.equiv Resolution.cfIso
  let : Module.Finite A Resolution.Ce :=
    Module.Finite.of_restrictScalars_finite ℚ A Resolution.Ce
  let : Module.Finite A Resolution.Cf :=
    Module.Finite.of_restrictScalars_finite ℚ A Resolution.Cf
  change Module.Finite A (Resolution.resObj n)
  cases n <;> dsimp [Resolution.resObj] <;> infer_instance

def tensorResolution : ProjectiveResolution simpleTensor :=
  TensorExt.resolution ℚ A A Resolution.projectiveResolution Resolution.projectiveResolution
    simple_resolution_term_finite simple_resolution_term_finite

def restrictedXResolution : ProjectiveResolution ((AlgebraInduction.res inclusionB).obj X) :=
  TensorDualResolution.transportResolution tensorResolution restrictionEquiv.toModuleIso

abbrev inducedSimpleChain :=
  ((AlgebraInduction.functor inclusionB).mapHomologicalComplex (.down ℕ)).obj
    tensorResolution.complex

def untwistedComparison : HomotopyEquiv
    ((EvaluatedSource.evaluationFunctor.mapHomologicalComplex (.down ℕ)).obj
      SignedSourceComparison.untwistedChain) inducedSimpleChain :=
  Enveloping.evaluatedInducedRegularComparison inclusionB X restrictedXResolution

abbrev chosenInducedChain :=
  ((InducedTwistedSocle.inductionFunctor.mapHomologicalComplex (.down ℕ)).obj
    InducedTwistedSocle.resolution.complex)

def signedComparison : HomotopyEquiv
    ((EvaluatedSource.evaluationFunctor.mapHomologicalComplex (.down ℕ)).obj
      chosenInducedChain) inducedSimpleChain :=
  ((EvaluatedSource.evaluationFunctor.mapHomotopyEquiv
    SignedSourceComparison.inducedHomotopy).trans
      (HomotopyEquiv.ofIso
        ((NatIso.mapHomologicalComplex
          (Functor.isoWhiskerLeft InducedTwistedSocle.inductionFunctor
            TwistEvaluation.actualComparison) (.down ℕ)).app
          SignedSourceComparison.regularResolution.complex))).trans untwistedComparison

theorem evaluated_exactAt_iff (n : ℕ) :
    ((EvaluatedSource.evaluationFunctor.mapHomologicalComplex (.down ℕ)).obj
      chosenInducedChain).ExactAt n ↔ inducedSimpleChain.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff_isZero_homology]
  exact (signedComparison.toHomologyIso n).isZero_iff

end
end TachikawaCharZero.EvaluatedInduction
