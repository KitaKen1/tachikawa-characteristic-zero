import TachikawaCharZero.TwoBranchBijectivity
import TachikawaCharZero.FinalTransfer
import OAI.RingTheory.Tachikawa.GenericTriangularCone

/-! The actual rational triangular algebra and finite totally acyclic cone.
This supplies the geometric part of the final witness. Nonprojectivity and
signed complete self-Hom vanishing remain explicit proof obligations. -/
namespace TachikawaCharZero.TriangularWitness
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory OAI.Tachikawa
open ScalingSocle SocleBimodule
open scoped ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

abbrev F := (TwoBranchFiber.F H₁ H₂ (by norm_num) (by norm_num)).obj
abbrev Lambda := Triangular.Alg F

theorem F_finite : Module.Finite ℚ F := by infer_instance
local instance finiteF : Module.Finite ℚ F := F_finite
local instance leftProjective : Module.Projective E (Enveloping.Obj F) :=
  (TwoBranchFiber.side_projective H₁ H₂ (by norm_num) (by norm_num)).1
local instance rightProjective : Module.Projective Eᵐᵒᵖ (Enveloping.Obj F) :=
  (TwoBranchFiber.side_projective H₁ H₂ (by norm_num) (by norm_num)).2

theorem Lambda_finite : Module.Finite ℚ Lambda := by infer_instance
local instance finiteLambda : Module.Finite ℚ Lambda := Lambda_finite

abbrev lift := TwoBranchAction.completeLift H₁ H₂ (by norm_num) (by norm_num)
abbrev cone := Triangular.cone F lift
abbrev Z := CokerAt cone 0
abbrev Gamma := FinalTransfer.Gamma Lambda
abbrev M := FinalTransfer.M cone

theorem cone_totallyAcyclic : TotallyAcyclic cone :=
  Triangular.cone_totallyAcyclic F lift
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)

theorem cone_finite (j : ℤ) : Module.Finite Lambda (cone.X j) :=
  Triangular.cone_finite F lift (StableSeam.finiteX.complete_finite TateProfile.form) j

theorem cone_projective (j : ℤ) : Module.Projective Lambda (cone.X j) :=
  Triangular.cone_projective F lift (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form) j

theorem Z_finite : Module.Finite ℚ Z := by
  let := FinalTransfer.coker_finite cone cone_finite
  exact Module.Finite.trans Lambda Z

theorem Gamma_finite : Module.Finite ℚ Gamma := by infer_instance

theorem Gamma_symmetric : SymmetricOver ℚ Gamma := FinalTransfer.Gamma_symmetric Lambda

theorem M_finite : Module.Finite ℚ M := FinalTransfer.M_finite cone cone_finite

/-- Acceptance theorem for this actual cone; its two remaining hypotheses
must be proved before asserting the unconditional rational Target. -/
theorem target_of_remaining
    (hn : ¬ Module.Projective Lambda Z)
    (van : ∀ a : ℤ, 0<a ∨ a≤ -2 →
      Subsingleton (VectorSplit.H (completeHom (k:=ℚ) cone (ModuleCat.of Lambda Z)) a)) :
    Target :=
  FinalTransfer.target_of_complete_resolution cone cone_totallyAcyclic
    cone_finite cone_projective hn van

end
end TachikawaCharZero.TriangularWitness
