import TachikawaCharZero.AlphaInjectivity
import TachikawaCharZero.CrossRestrictionRight
import TachikawaCharZero.ExtIndex

/-! A basis of actual Yoneda monomials, constructed from injective alpha
multiplication and the beta power outside its image. No identification
with the previously chosen Kunneth coordinates or interchange law is used. -/
namespace TachikawaCharZero.MonomialBasis
noncomputable section
open CategoryTheory CategoryTheory.Abelian Module TensorProfile SplitInflation AlphaInjectivity
open scoped ModuleCat.Algebra

def monomials : (m : ℕ) → Fin (m+1) → Ext X₂ X₂ (3*m)
  | 0 => fun _ => rightPower 0
  | m+1 => Fin.cons (rightPower (m+1)) (fun i => alphaMap m (monomials m i))

theorem monomials_zero (m : ℕ) : monomials m 0 = rightPower m := by
  cases m <;> rfl

theorem monomials_succ (m : ℕ) (i : Fin (m+1)) :
    monomials (m+1) i.succ = alphaMap m (monomials m i) := rfl

theorem leftPower_comp_degree (a b c : ℕ) (h : a+b=c) :
    (leftPower a).comp (leftPower b) (show 3*a+3*b=3*c by omega) = leftPower c := by
  rw [leftPower, leftPower, ← externalMap_comp, Induced.tauPower_comp_aux a b c h]
  rfl

theorem alpha_mixed_product (a b m : ℕ) (h : a+b=m) :
    alphaMap m ((leftPower a).comp (rightPower b) (by omega)) =
      (leftPower (a+1)).comp (rightPower b) (by omega) := by
  change alpha.comp ((leftPower a).comp (rightPower b) (show 3*a+3*b=3*m by omega))
    (show 3+3*m=3*(m+1) by omega) = _
  rw [← Ext.comp_assoc (a₁₂ := 3*(a+1)) _ _ _ (by omega) (by omega) (by omega)]
  have hp : alpha.comp (leftPower a) (show 3+3*a=3*(a+1) by omega) =
      leftPower (a+1) := by
    exact leftPower_comp_degree 1 a (a+1) (by omega)
  rw [hp]

theorem monomials_eq_product (m : ℕ) (i : Fin (m+1)) :
    monomials m i = (leftPower i.val).comp (rightPower (m-i.val)) (by omega) := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [monomials_zero, Fin.val_zero, leftPower_zero, Ext.mk₀_id_comp]
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [monomials_zero, Fin.val_zero, Nat.sub_zero, leftPower_zero, Ext.mk₀_id_comp]
    · rw [monomials_succ, ih, alpha_mixed_product j.val (m-j.val) m (by omega)]
      simp only [Fin.val_succ]
      exact ExtIndex.comp_right_index _ rightPower (by omega) _ _

theorem monomials_linearIndependent (m : ℕ) : LinearIndependent ℚ (monomials m) := by
  induction m with
  | zero =>
    let : Subsingleton (Fin (0+1)) := ⟨fun i j => Fin.ext (by
      have hi := i.isLt
      have hj := j.isLt
      omega)⟩
    exact LinearIndependent.of_subsingleton 0 (rightPower_ne_zero 0)
  | succ m ih =>
    apply (ih.map' (alphaMap m) (LinearMap.ker_eq_bot.mpr (alphaMap_injective m))).finCons
    intro hspan
    have hr : Submodule.span ℚ (Set.range (fun i => alphaMap m (monomials m i))) ≤
        LinearMap.range (alphaMap m) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨monomials m i, rfl⟩
    obtain ⟨x, hx⟩ := hr hspan
    exact rightPower_not_in_alpha_range m ⟨x, hx⟩

def monomialBasis (m : ℕ) : Basis (Fin (m+1)) ℚ (Ext X₂ X₂ (3*m)) :=
  basisOfLinearIndependentOfCardEqFinrank (monomials_linearIndependent m)
    (by simpa using (TensorProfile.ext_multiple_finrank m).symm)

theorem monomialBasis_apply (m : ℕ) (i : Fin (m+1)) :
    monomialBasis m i = monomials m i := by
  simp [monomialBasis]

theorem monomial_expansion (m : ℕ) (x : Ext X₂ X₂ (3*m)) :
    x = ∑ i, (monomialBasis m).repr x i • monomials m i := by
  simpa only [monomialBasis_apply] using ((monomialBasis m).sum_repr x).symm

theorem monomials_ne_zero (m : ℕ) (i : Fin (m+1)) : monomials m i ≠ 0 :=
  (monomials_linearIndependent m).ne_zero i

theorem alpha_basis_shift (m : ℕ) (i : Fin (m+1)) :
    alphaMap m (monomialBasis m i) = monomialBasis (m+1) i.succ := by
  simp only [monomialBasis_apply, monomials_succ]

theorem beta_basis_zero (m : ℕ) : monomialBasis m 0 = rightPower m := by
  rw [monomialBasis_apply, monomials_zero]

end
end TachikawaCharZero.MonomialBasis
