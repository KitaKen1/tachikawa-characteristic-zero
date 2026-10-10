import TachikawaCharZero.PeriodicExt

/-! Normalized powers of the nonzero degree-three Yoneda class.
The composition induction and coordinate formula are adapted from OpenAI
Math's Tachikawa/Period.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
All statements here concern the checked rational T-character module. -/
namespace TachikawaCharZero.Induced
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

def tauPower (m : ℕ) : Ext X X (3*m) :=
  (extMultiple m).symm 1

theorem tauPower_zero : tauPower 0 = Ext.mk₀ (𝟙 X) := by
  change Ext.mk₀ ((1:ℚ) • 𝟙 X) = _
  rw [one_smul]

theorem tauPower_ne_zero (m : ℕ) : tauPower m ≠ 0 := by
  intro h
  have he := congrArg (extMultiple m) h
  simp only [tauPower,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero he

theorem tauPower_succ (m : ℕ) : tauPower (m+1) =
    (tau).comp (tauPower m) (by omega) := by
  unfold tauPower
  simp only [extMultiple]
  have h : 3*(m+1) = 3*m+3 := by omega
  generalize he : extMultiple m = e
  cases h
  change period (3*m) (e.symm 1) = _
  exact period_eq_tau_comp (3*m) (e.symm 1)

theorem tauPower_one : tauPower 1=tau := by
  simpa only [tauPower_zero,Ext.comp_mk₀_id] using tauPower_succ 0

theorem tauPower_comp_aux (m n c : ℕ) (hc : m+n=c) :
    (tauPower m).comp (tauPower n) (by omega) =
      tauPower c := by
  induction m generalizing c with
  | zero =>
    have hc' : n = c := by omega
    subst hc'
    rw [tauPower_zero]
    simpa only [Nat.zero_add] using Ext.mk₀_id_comp (tauPower n)
  | succ m ih =>
    have hc' : c = (m+n)+1 := by omega
    subst hc'
    rw [tauPower_succ,Ext.comp_assoc (a₂₃ := 3*(m+n)) _ _ _ (by omega) (by omega) (by omega),
      ih (m+n) rfl]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (tauPower_succ (m+n)).symm

theorem tauPower_comp (m n : ℕ) :
    (tauPower m).comp (tauPower n) (by omega) =
      tauPower (m+n) := tauPower_comp_aux m n (m+n) rfl

theorem eq_smul_tauPower (m : ℕ) (x : Ext X X (3*m)) :
    x = extMultiple m x • tauPower m := by
  apply (extMultiple m).injective
  rw [map_smul]
  simp only [tauPower,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]

theorem tau_coordinates_comp (m n : ℕ)
    (x : Ext X X (3*m))
    (y : Ext X X (3*n)) :
    extMultiple (m+n) (x.comp y (by omega)) =
      extMultiple m x * extMultiple n y := by
  have he : x.comp y (show 3*m+3*n=3*(m+n) by omega) =
      (extMultiple m x * extMultiple n y) •
        tauPower (m+n) := by
    nth_rw 1 [eq_smul_tauPower m x,eq_smul_tauPower n y]
    rw [Ext.smul_comp,Ext.comp_smul,tauPower_comp,smul_smul]
  rw [he,map_smul]
  simp only [tauPower,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]

end
end TachikawaCharZero.Induced
