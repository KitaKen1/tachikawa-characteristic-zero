import TachikawaCharZero.CrossRestriction

/-! The right restriction separates a new right-axis power from every
class obtained by left multiplication with alpha. This supplies the
quotient direction for an inductive monomial basis. Injectivity of
alpha multiplication is a separate obligation. -/
namespace TachikawaCharZero.SplitInflation
noncomputable section
open CategoryTheory CategoryTheory.Abelian Induced TensorProfile OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

theorem crossProjectionRight :
    projectionLeft.comp inclusionRight = scalarInclusion.comp characterT := by
  apply AlgHom.ext
  intro a
  change projectionLeft (1 ⊗ₜ[ℚ] a) = algebraMap ℚ T (characterT a)
  rw [projectionLeft_tmul, Algebra.smul_def, mul_one]

def crossRestrictionRightIso : inflateLeft ⋙ restrictRight ≅
    groundRestriction ⋙ characterRestriction :=
  (ModuleCat.restrictScalarsComp inclusionRight.toRingHom projectionLeft.toRingHom).symm ≪≫
    ModuleCat.restrictScalarsComp' characterT.toRingHom scalarInclusion.toRingHom _
      (congrArg AlgHom.toRingHom crossProjectionRight)

theorem cross_right_ext_zero (M N : ModuleCat T) (n : ℕ) (x : Ext M N (n+1)) :
    (x.mapExactFunctor inflateLeft).mapExactFunctor restrictRight = 0 := by
  have h : x.mapExactFunctor (groundRestriction ⋙ characterRestriction) = 0 := by
    rw [Ext.comp_mapExactFunctor]
    let : Subsingleton (Ext (groundRestriction.obj M) (groundRestriction.obj N) (n+1)) :=
      Ext.subsingleton_of_projective _ _ n
    rw [Subsingleton.elim (x.mapExactFunctor groundRestriction) 0]
    simp
  rw [← Ext.comp_mapExactFunctor]
  exact ExtTransport.map_zero_of_natIso _ crossRestrictionRightIso.symm x h

def recoverRight (n : ℕ) : Ext X₂ X₂ n →ₗ[ℚ] Ext X X n :=
  (ExtTransport.conjugateLinearMap ℚ (retractRight.app X) n).comp
    ((restrictRight.mapExtLinearMap ℚ (inflateRight.obj X) (inflateRight.obj X) n).comp
      (ExtTransport.conjugateLinearMap ℚ inflatedRightIso.symm n))

theorem recoverRight_externalRight (n : ℕ) (x : Ext X X n) :
    recoverRight n (externalRight n x) = x := by
  change ExtTransport.conjugate (retractRight.app X)
    ((ExtTransport.conjugate inflatedRightIso.symm
      (ExtTransport.conjugate inflatedRightIso (x.mapExactFunctor inflateRight))).mapExactFunctor
        restrictRight) = x
  rw [ExtTransport.conjugate_symm]
  exact restore_ext inflateRight restrictRight retractRight x

theorem recoverRight_externalLeft (n : ℕ) (x : Ext X X (n+1)) :
    recoverRight (n+1) (externalLeft (n+1) x) = 0 := by
  change ExtTransport.conjugate (retractRight.app X)
    ((ExtTransport.conjugate inflatedRightIso.symm
      (ExtTransport.conjugate inflatedLeftIso (x.mapExactFunctor inflateLeft))).mapExactFunctor
        restrictRight) = 0
  rw [ExtTransport.map_conjugate, ExtTransport.map_conjugate, cross_right_ext_zero]
  simp [ExtTransport.conjugate_zero]

theorem recoverRight_rightPower (m : ℕ) : recoverRight (3*m) (rightPower m) = tauPower m :=
  recoverRight_externalRight _ _

theorem recoverRight_leftPower (m : ℕ) (hm : 0 < m) :
    recoverRight (3*m) (leftPower m) = 0 := by
  have h (n : ℕ) (hn : 0 < n) (x : Ext X X n) :
      recoverRight n (externalLeft n x) = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact recoverRight_externalLeft j x
  exact h (3*m) (by omega) (tauPower m)

theorem recoverRight_comp {a b c : ℕ} (x : Ext X₂ X₂ a) (y : Ext X₂ X₂ b) (h : a+b=c) :
    recoverRight c (x.comp y h) = (recoverRight a x).comp (recoverRight b y) h := by
  change ExtTransport.conjugate (retractRight.app X)
    ((ExtTransport.conjugate inflatedRightIso.symm (x.comp y h)).mapExactFunctor restrictRight) = _
  rw [ExtTransport.conjugate_comp, Ext.mapExactFunctor_comp, ExtTransport.conjugate_comp]
  rfl

theorem recoverRight_alpha : recoverRight 3 alpha = 0 := recoverRight_leftPower 1 (by omega)

theorem recoverRight_alpha_comp {n c : ℕ} (x : Ext X₂ X₂ n) (h : 3+n=c) :
    recoverRight c (alpha.comp x h) = 0 := by
  rw [recoverRight_comp, recoverRight_alpha, Ext.zero_comp]

theorem rightPower_not_in_alpha_range (m : ℕ) :
    ¬ ∃ x : Ext X₂ X₂ (3*m), alpha.comp x (show 3+3*m=3*(m+1) by omega) =
      rightPower (m+1) := by
  rintro ⟨x,h⟩
  have hh := congrArg (recoverRight (3*(m+1))) h
  rw [recoverRight_alpha_comp, recoverRight_rightPower] at hh
  exact tauPower_ne_zero (m+1) hh.symm

end
end TachikawaCharZero.SplitInflation
