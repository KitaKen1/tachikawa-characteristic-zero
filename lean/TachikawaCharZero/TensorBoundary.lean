import TachikawaCharZero.TensorInflation

/-! Kunneth vanishing for the actual tensor-mapped period-three sequences.
The projective corner Tf contributes only its degree-zero Ext in the left
factor; thus its tensor with S has no Ext in degrees 3m+2. -/
namespace TachikawaCharZero.TensorBoundary
noncomputable section
open CategoryTheory CategoryTheory.Abelian Induced TensorProfile TensorInflation OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

def boundaryFinite : FiniteModule ℚ T where
  obj := B₂Obj
  finite := by
    let : Module.Finite ℚ B₂ := Module.Finite.of_injective
      (B₂.subtype.restrictScalars ℚ) B₂.subtype_injective
    exact Module.Finite.of_restrictScalars_finite ℚ T B₂

def teFinite : FiniteModule ℚ T where
  obj := ModuleCat.of T TE
  finite := Module.Finite.of_restrictScalars_finite ℚ T TE

def tfFinite : FiniteModule ℚ T where
  obj := ModuleCat.of T TF
  finite := Module.Finite.of_restrictScalars_finite ℚ T TF

theorem tensor_ext_zero_of_left (M : FiniteModule ℚ T)
    (hzero : ∀ i, Subsingleton (Ext M.obj X i)) (n : ℕ) :
    Subsingleton (Ext (tensorLeft.obj M.obj) X₂ n) := by
  have (t : SignedTotalPairing.Diag n) :
      Subsingleton (Ext M.obj X t.val.1 ⊗[ℚ] Ext X X t.val.2) := by
    let := hzero t.val.1
    infer_instance
  exact (TensorExt.extKunneth M.projectiveResolution P n).injective.subsingleton

theorem boundary_ext_zero (n : ℕ) :
    Subsingleton (Ext (tensorLeft.obj B₂Obj) X₂ n) :=
  tensor_ext_zero_of_left boundaryFinite Induced.boundary_ext_zero n

theorem te_ext_zero (n : ℕ) :
    Subsingleton (Ext (tensorLeft.obj (ModuleCat.of T TE)) X₂ n) :=
  tensor_ext_zero_of_left teFinite Induced.te_ext_zero n

theorem tf_ext_zero (m : ℕ) :
    Subsingleton (Ext (tensorLeft.obj (ModuleCat.of T TF)) X₂ (3*m+2)) := by
  have (t : SignedTotalPairing.Diag (3*m+2)) :
      Subsingleton (Ext tfFinite.obj X t.val.1 ⊗[ℚ]
        Ext simpleFinite.obj X t.val.2) := by
    change Subsingleton (Ext (ModuleCat.of T TF) X t.val.1 ⊗[ℚ] Ext X X t.val.2)
    have ht := t.property
    change t.val.1+t.val.2=3*m+2 at ht
    cases hi : t.val.1 with
    | zero =>
      let := Induced.self_ext_off_multiples t.val.2 (by omega)
      infer_instance
    | succ i =>
      let := Ext.subsingleton_of_projective (ModuleCat.of T TF) X i
      infer_instance
  exact (TensorExt.extKunneth tfFinite.projectiveResolution P (3*m+2)).injective.subsingleton

end
end TachikawaCharZero.TensorBoundary
