import TachikawaCharZero.TwistSideRestriction
import TachikawaCharZero.SocleBimodule
import TachikawaCharZero.EvaluatedSource

/-! An involutive right twist fixing X disappears under balanced tensor
evaluation. The comparison is the identity on tensor generators and is
natural in the actual bimodule. No tensor exactness assumption is used. -/
namespace TachikawaCharZero.TwistEvaluation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

section Generic
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (σ : R ≃ₐ[k] R) (hσ : Function.Involutive σ)
  (X : ModuleCat R) (hX : ∀ r : R, ∀ x : X, σ r • x = r • x)

def forward (M : ModuleCat (Enveloping.Alg k R R)) :
    Enveloping.evalObj X ((TwistSideRestriction.twist σ).obj M) ⟶
      Enveloping.evalObj X M :=
  ModuleCat.ofHom (BalancedTensor.lift
    ((BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Enveloping.Obj M) (N := X)).comp
        (TwistSideRestriction.leftObjIso σ M).hom.hom) (by
    intro r m x
    change BalancedTensor.mk (k := k) (R := R) (S := R)
      ((MulOpposite.op (σ r)) • (show Enveloping.Obj M from m)) x =
        BalancedTensor.mk (show Enveloping.Obj M from m) (r • x)
    rw [BalancedTensor.balance,hX]))

def backward (M : ModuleCat (Enveloping.Alg k R R)) :
    Enveloping.evalObj X M ⟶
      Enveloping.evalObj X ((TwistSideRestriction.twist σ).obj M) :=
  ModuleCat.ofHom (BalancedTensor.lift
    ((BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Enveloping.Obj ((TwistSideRestriction.twist σ).obj M)) (N := X)).comp
        (TwistSideRestriction.leftObjIso σ M).inv.hom) (by
    intro r m x
    have hm : (show Enveloping.Obj ((TwistSideRestriction.twist σ).obj M) from
        (MulOpposite.op r • m)) = MulOpposite.op (σ r) •
          (show Enveloping.Obj ((TwistSideRestriction.twist σ).obj M) from m) := by
      change ((1 : R) ⊗ₜ[k] MulOpposite.op r) • (show M from m) =
        ((1 : R) ⊗ₜ[k] MulOpposite.op (σ (σ r))) • (show M from m)
      rw [hσ]
    change BalancedTensor.mk (k := k) (R := R) (S := R)
      (show Enveloping.Obj ((TwistSideRestriction.twist σ).obj M) from
        (MulOpposite.op r • m)) x = _
    rw [hm,BalancedTensor.balance,hX]
    rfl))

def objIso (M : ModuleCat (Enveloping.Alg k R R)) :
    Enveloping.evalObj X ((TwistSideRestriction.twist σ).obj M) ≅
      Enveloping.evalObj X M where
  hom := forward σ X hX M
  inv := backward σ hσ X hX M
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

def comparison : TwistSideRestriction.twist σ ⋙ Enveloping.evaluation (k := k) X ≅
    Enveloping.evaluation (k := k) X :=
  NatIso.ofComponents (objIso σ hσ X hX) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl)

end Generic

open ScalingSocle SocleBimodule SignedTrivialAutomorphism
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

theorem character_signedT (a : T) : Starting.T_character (signedT a) =
    Starting.T_character a := by
  change Resolution.character (sigma (2 : ℚ) a.fst) = Resolution.character a.fst
  simp [Resolution.character,sigma,signedLinearEquiv,signed,signCoeff]

theorem character_signedE (a : E) : characterE (signedE a) = characterE a := by
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    change Starting.T_character (signedT a) * Starting.T_character (signedT b) =
      Starting.T_character a * Starting.T_character b
    rw [character_signedT,character_signedT]
  | add a b ha hb => simp only [map_add,ha,hb]

theorem signed_fixed_X (r : E) (x : X) : signedE r • x = r • x := by
  apply TensorProfile.groundEquiv.injective
  rw [ground_action,ground_action,character_signedE]

def actualComparison : SignedInductionComparison.signedRestrictionE ⋙
    EvaluatedSource.evaluationFunctor ≅ EvaluatedSource.evaluationFunctor :=
  comparison signedE signedE_involutive X signed_fixed_X

end
end TachikawaCharZero.TwistEvaluation
