import TachikawaCharZero.SplitInflation

/-! Restriction to one tensor factor kills positive classes inflated from
the other factor: the composite factors through rational vector spaces.
This separates the actual Yoneda axes without assuming Künneth naturality
or a graded-commutativity statement. -/
namespace TachikawaCharZero.SplitInflation
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Module
open Induced TensorProfile OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

def scalarInclusion : ℚ →ₐ[ℚ] T := Algebra.ofId ℚ T
abbrev groundRestriction := AlgebraInduction.res scalarInclusion
abbrev characterRestriction := AlgebraInduction.res characterT

theorem crossProjection : projectionRight.comp inclusionLeft = scalarInclusion.comp characterT := by
  apply AlgHom.ext
  intro a
  change projectionRight (a ⊗ₜ[ℚ] 1) = algebraMap ℚ T (characterT a)
  rw [projectionRight_tmul, Algebra.smul_def, mul_one]

def crossRestrictionIso : inflateRight ⋙ restrictLeft ≅
    groundRestriction ⋙ characterRestriction :=
  (ModuleCat.restrictScalarsComp inclusionLeft.toRingHom projectionRight.toRingHom).symm ≪≫
    ModuleCat.restrictScalarsComp' characterT.toRingHom scalarInclusion.toRingHom _
      (congrArg AlgHom.toRingHom crossProjection)

theorem cross_ext_zero (M N : ModuleCat T) (n : ℕ) (x : Ext M N (n+1)) :
    (x.mapExactFunctor inflateRight).mapExactFunctor restrictLeft = 0 := by
  have h : x.mapExactFunctor (groundRestriction ⋙ characterRestriction) = 0 := by
    rw [Ext.comp_mapExactFunctor]
    let : Subsingleton (Ext (groundRestriction.obj M) (groundRestriction.obj N) (n+1)) :=
      Ext.subsingleton_of_projective _ _ n
    rw [Subsingleton.elim (x.mapExactFunctor groundRestriction) 0]
    simp
  rw [← Ext.comp_mapExactFunctor]
  exact ExtTransport.map_zero_of_natIso _ crossRestrictionIso.symm x h

def recoverLeft (n : ℕ) : Ext X₂ X₂ n →ₗ[ℚ] Ext X X n :=
  (ExtTransport.conjugateLinearMap ℚ (retractLeft.app X) n).comp
    ((restrictLeft.mapExtLinearMap ℚ (inflateLeft.obj X) (inflateLeft.obj X) n).comp
      (ExtTransport.conjugateLinearMap ℚ inflatedLeftIso.symm n))

theorem recoverLeft_externalLeft (n : ℕ) (x : Ext X X n) :
    recoverLeft n (externalLeft n x) = x := by
  change ExtTransport.conjugate (retractLeft.app X)
    ((ExtTransport.conjugate inflatedLeftIso.symm
      (ExtTransport.conjugate inflatedLeftIso (x.mapExactFunctor inflateLeft))).mapExactFunctor
        restrictLeft) = x
  rw [ExtTransport.conjugate_symm]
  exact restore_ext inflateLeft restrictLeft retractLeft x

theorem recoverLeft_externalRight (n : ℕ) (x : Ext X X (n+1)) :
    recoverLeft (n+1) (externalRight (n+1) x) = 0 := by
  change ExtTransport.conjugate (retractLeft.app X)
    ((ExtTransport.conjugate inflatedLeftIso.symm
      (ExtTransport.conjugate inflatedRightIso (x.mapExactFunctor inflateRight))).mapExactFunctor
        restrictLeft) = 0
  rw [ExtTransport.map_conjugate, ExtTransport.map_conjugate, cross_ext_zero]
  simp [ExtTransport.conjugate_zero]

theorem recoverLeft_leftPower (m : ℕ) : recoverLeft (3*m) (leftPower m) = tauPower m :=
  recoverLeft_externalLeft _ _

theorem recoverLeft_rightPower (m : ℕ) (hm : 0 < m) :
    recoverLeft (3*m) (rightPower m) = 0 := by
  have h (n : ℕ) (hn : 0 < n) (x : Ext X X n) :
      recoverLeft n (externalRight n x) = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact recoverLeft_externalRight k x
  exact h (3*m) (by omega) (tauPower m)

theorem powers_ne (m : ℕ) (hm : 0 < m) : leftPower m ≠ rightPower m := by
  intro h
  have hh := congrArg (recoverLeft (3*m)) h
  rw [recoverLeft_leftPower, recoverLeft_rightPower m hm] at hh
  exact tauPower_ne_zero m hh

theorem alpha_ne_beta : alpha ≠ beta := powers_ne 1 (by omega)

theorem powers_linearIndependent (m : ℕ) (hm : 0 < m) :
    LinearIndependent ℚ ![leftPower m, rightPower m] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hh := congrArg (recoverLeft (3*m)) h
  simp only [map_add, map_smul, map_zero, recoverLeft_leftPower,
    recoverLeft_rightPower m hm, smul_zero, add_zero] at hh
  have hs : s = 0 := (smul_eq_zero.mp hh).resolve_right (tauPower_ne_zero m)
  rw [hs, zero_smul, zero_add] at h
  exact ⟨hs, (smul_eq_zero.mp h).resolve_right (rightPower_ne_zero m)⟩

theorem alpha_beta_linearIndependent : LinearIndependent ℚ ![alpha, beta] :=
  powers_linearIndependent 1 (by omega)

def generatorBasis : Basis (Fin 2) ℚ (Ext X₂ X₂ 3) :=
  basisOfLinearIndependentOfCardEqFinrank alpha_beta_linearIndependent
    (by simpa using (TensorProfile.ext_multiple_finrank 1).symm)

theorem generatorBasis_apply (a : Fin 2) : generatorBasis a = ![alpha, beta] a := by
  simp [generatorBasis]

theorem alpha_beta_span (x : Ext X₂ X₂ 3) :
    x = generatorBasis.repr x 0 • alpha + generatorBasis.repr x 1 • beta := by
  have h := generatorBasis.sum_repr x
  simpa only [Fin.sum_univ_two, generatorBasis_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h.symm

end
end TachikawaCharZero.SplitInflation
