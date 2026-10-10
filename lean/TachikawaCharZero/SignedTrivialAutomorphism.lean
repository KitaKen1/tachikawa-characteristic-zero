import TachikawaCharZero.ScalingSocle

/-! Extend a base algebra automorphism to its trivial extension using
contragredient transport of the dual. The actual rational signed twist
therefore extends from B to E. This is algebraic input for a future
comparison of signed and untwisted induced complexes; that comparison
and high-degree exactness are not asserted here. -/
namespace TachikawaCharZero.SignedTrivialAutomorphism
noncomputable section
open OAI.Tachikawa
open scoped TensorProduct

section Generic
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

def lift (σ : R ≃ₐ[k] R) : TrivialExtension k R ≃ₐ[k] TrivialExtension k R where
  toFun a := ⟨σ a.fst,a.snd.comp σ.symm.toLinearMap⟩
  invFun a := ⟨σ.symm a.fst,a.snd.comp σ.toLinearMap⟩
  left_inv a := by
    apply TrivSqZeroExt.ext
    · exact σ.symm_apply_apply a.fst
    · ext r
      exact congrArg a.snd (σ.symm_apply_apply r)
  right_inv a := by
    apply TrivSqZeroExt.ext
    · exact σ.apply_symm_apply a.fst
    · ext r
      exact congrArg a.snd (σ.apply_symm_apply r)
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact σ.map_mul a.fst b.fst
    · ext r
      change b.snd (σ.symm r*a.fst) + a.snd (b.fst*σ.symm r) =
        b.snd (σ.symm (r*σ a.fst)) + a.snd (σ.symm (σ b.fst*r))
      simp only [map_mul,σ.symm_apply_apply]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · exact σ.map_add a.fst b.fst
    · ext r
      rfl
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact σ.commutes c
    · ext r
      rfl

theorem lift_inl (σ : R ≃ₐ[k] R) (a : R) :
    lift σ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (σ a) := by
  apply TrivSqZeroExt.ext
  · rfl
  · ext r
    rfl

theorem lift_involutive (σ : R ≃ₐ[k] R) (hσ : Function.Involutive σ) :
    Function.Involutive (lift σ) := by
  intro a
  apply TrivSqZeroExt.ext
  · exact hσ a.fst
  · ext r
    change a.snd (σ.symm (σ.symm r)) = a.snd r
    have hi (x : R) : σ.symm x = σ x := by
      apply σ.injective
      rw [σ.apply_symm_apply,hσ]
    rw [hi,hi,hσ]
end Generic

open ScalingSocle

def signedT : T ≃ₐ[ℚ] T := lift (sigma (2 : ℚ))
def signedE : E ≃ₐ[ℚ] E := Algebra.TensorProduct.congr signedT signedT

theorem signedT_involutive : Function.Involutive signedT :=
  lift_involutive _ (sigma_involutive (2 : ℚ))

theorem signedE_involutive : Function.Involutive signedE := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change signedT (signedT a) ⊗ₜ[ℚ] signedT (signedT b) = a ⊗ₜ[ℚ] b
    rw [signedT_involutive,signedT_involutive]
  | add a b ha hb => simp only [map_add,ha,hb]

theorem signedE_inclusion (b : ScalingSocle.B) :
    signedE (inclusionB b) = inclusionB (TwistedFactorization.theta b) := by
  induction b using TensorProduct.inductionOn with
  | tmul a b =>
    change lift (sigma (2 : ℚ)) (TrivSqZeroExt.inl a) ⊗ₜ[ℚ]
      lift (sigma (2 : ℚ)) (TrivSqZeroExt.inl b) =
      TrivSqZeroExt.inl (sigma (2 : ℚ) a) ⊗ₜ[ℚ] TrivSqZeroExt.inl (sigma (2 : ℚ) b)
    rw [lift_inl,lift_inl]
  | add a b ha hb => simp only [map_add,ha,hb]

end
end TachikawaCharZero.SignedTrivialAutomorphism
