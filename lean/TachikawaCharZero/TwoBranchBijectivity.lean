import TachikawaCharZero.TwoBranchHom

/-! The actual signed Delta has the full injectivity/surjectivity ranges
needed by a cone boundary criterion. No replacement scalar model is used.
Identification with the final triangular cone remains a separate obligation. -/
namespace TachikawaCharZero.TwoBranchBijectivity
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev delta (ε : ℚ) (a : ℤ) :=
  TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num) ε a

theorem surjective_of_weights (ε : ℚ) (a : ℤ) (hε : ε ≠ 0)
    (hc : TwistedBranchWeights.weight H₁ a ≠ TwistedBranchWeights.weight H₂ a)
    (hm2 : a ≠ -2) : Function.Surjective (delta ε a) :=
  (TwoBranchCancellation.actual_properties ε a hε hc).2.2.mpr
    (TwoBranchHom.pair_injective H₁ H₂ (by norm_num) (by norm_num) a hm2)

theorem surjective_of_zero_input (ε : ℚ) (a : ℤ) (hm2 : a ≠ -2)
    (hz : Subsingleton (TateProfile.Tate a)) : Function.Surjective (delta ε a) := by
  let := hz
  let : Subsingleton (OAI.Tachikawa.VectorSplit.H
      (TwoBranchDelta.fiberComplex H₁ H₂ (by norm_num) (by norm_num)) a) :=
    (TwoBranchHom.pair_injective H₁ H₂ (by norm_num) (by norm_num) a hm2).subsingleton
  intro x
  exact ⟨0,Subsingleton.elim _ _⟩

theorem surjective (ε : ℚ) (a : ℤ) (hε : ε ≠ 0) (hm2 : a ≠ -2) :
    Function.Surjective (delta ε a) := by
  by_cases h0 : a = 0
  · subst a
    exact TwoBranchHom.delta_zero_surjective H₁ H₂ (by norm_num) (by norm_num) ε hε
  · cases a with
    | ofNat n =>
      by_cases hn : n%3 = 0
      · have hn0 : n ≠ 0 := by
          intro he
          apply h0
          simp [he]
        have hm : 0 < n/3 := by omega
        rw [show Int.ofNat n = ((3*(n/3):ℕ):ℤ) by
          rw [Int.ofNat_eq_natCast]
          omega]
        exact surjective_of_weights _ _ hε
          (TwoBranchCancellation.weights_distinct_positive (n/3) hm) (by omega)
      · exact surjective_of_zero_input ε _ hm2 (TateProfile.nonnegative_zero n hn)
    | negSucc n =>
      by_cases hn : n%3 = 0
      · rw [show Int.negSucc n = -((3*(n/3):ℕ):ℤ)-1 by omega]
        exact surjective_of_weights _ _ hε
          (TwoBranchCancellation.weights_distinct_negative (n/3)) (by omega)
      · apply surjective_of_zero_input ε _ hm2
        rw [show Int.negSucc n = -(n:ℤ)-1 by omega]
        exact TateProfile.negative_zero n hn

theorem bijective (ε : ℚ) (a : ℤ) (hε : ε ≠ 0) (h0 : a ≠ 0) (hm2 : a ≠ -2) :
    Function.Bijective (delta ε a) :=
  ⟨TwoBranchCancellation.nonzero_degree ε a h0 hε,surjective ε a hε hm2⟩

theorem signed_surjective (a : ℤ) (hm2 : a ≠ -2) :
    Function.Surjective (delta (SignedDownHom.sign (k:=ℚ) a) a) :=
  surjective _ a (SignedDeltaMatrices.sign_ne_zero a) hm2

theorem signed_bijective (a : ℤ) (h0 : a ≠ 0) (hm2 : a ≠ -2) :
    Function.Bijective (delta (SignedDownHom.sign (k:=ℚ) a) a) :=
  bijective _ a (SignedDeltaMatrices.sign_ne_zero a) h0 hm2

theorem signed_vanishing_ranges (a : ℤ) (ha : 0 < a ∨ a ≤ -2) :
    Function.Injective (delta (SignedDownHom.sign (k:=ℚ) a) a) ∧
    Function.Surjective (delta (SignedDownHom.sign (k:=ℚ) (a-1)) (a-1)) :=
  ⟨TwoBranchCancellation.signed_nonzero_degree a (by omega),
   signed_surjective (a-1) (by omega)⟩

end
end TachikawaCharZero.TwoBranchBijectivity
