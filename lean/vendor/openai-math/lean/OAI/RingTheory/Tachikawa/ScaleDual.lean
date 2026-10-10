import OAI.RingTheory.Tachikawa.Symmetry

/-! Characteristic-independent excerpt from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Only imports and outer wrappers are replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.TrivialExtension
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

def scaleDual (H : k) (hH : H ≠ 0) : TrivialExtension k R ≃ₐ[k] TrivialExtension k R where
  toFun a := ⟨a.fst, H • a.snd⟩
  invFun a := ⟨a.fst, H⁻¹ • a.snd⟩
  left_inv a := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · change H⁻¹ • (H • a.snd) = a.snd
      simp [smul_smul, hH]
  right_inv a := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · change H • (H⁻¹ • a.snd) = a.snd
      simp [smul_smul, hH]
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · ext r
      change H * (b.snd (r*a.fst) + a.snd (b.fst*r)) =
        H*b.snd (r*a.fst) + H*a.snd (b.fst*r)
      exact mul_add _ _ _
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · exact smul_add H a.snd b.snd
  commutes' c := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · exact smul_zero H

@[simp] lemma scaleDual_fst (H : k) (hH : H ≠ 0) (a : TrivialExtension k R) :
    (scaleDual H hH a).fst = a.fst := rfl
@[simp] lemma scaleDual_snd (H : k) (hH : H ≠ 0) (a : TrivialExtension k R) :
    (scaleDual H hH a).snd = H • a.snd := rfl
@[simp] lemma scaleDual_inl (H : k) (hH : H ≠ 0) (a : R) :
    scaleDual H hH (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rfl
  · exact smul_zero H
@[simp] lemma scaleDual_inr (H : k) (hH : H ≠ 0) (a : DualBimodule k R) :
    scaleDual H hH (TrivSqZeroExt.inr a) = TrivSqZeroExt.inr (H • a) := rfl

end Tachikawa.TrivialExtension

end
end OAI
