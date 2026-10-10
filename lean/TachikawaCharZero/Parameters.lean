import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace TachikawaCharZero

abbrev q : ℚ := 2
abbrev H₁ : ℚ := 2
abbrev H₂ : ℚ := 3

theorem q_ne_zero : q ≠ 0 := by norm_num [q]
theorem one_add_q_ne_zero : 1 + q ≠ 0 := by norm_num [q]

theorem abs_neg_two_pow (m : ℕ) : |(-2 : ℚ) ^ m| = (2 : ℚ) ^ m := by
  rw [abs_pow]
  norm_num

theorem resolution_right_coefficient_ne_zero (m : ℕ) :
    1 - 4 * (-2 : ℚ) ^ m ≠ 0 := by
  intro h
  have he : (-2 : ℚ) ^ m = 1 / 4 := by linarith
  have ha := congrArg abs he
  rw [abs_neg_two_pow] at ha
  norm_num at ha
  have hle : (1 : ℚ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  linarith

theorem resolution_left_coefficient_ne_zero (m : ℕ) (hm : 0 < m) :
    1 - (-2 : ℚ) ^ m ≠ 0 := by
  intro h
  have he : (-2 : ℚ) ^ m = 1 := by linarith
  have ha := congrArg abs he
  rw [abs_neg_two_pow] at ha
  norm_num at ha
  have hlt : (1 : ℚ) < 2 ^ m := one_lt_pow₀ (by norm_num) (by omega)
  linarith

theorem twist_pow_lt (m : ℕ) (hm : 0 < m) : H₁ ^ m < H₂ ^ m := by
  exact pow_lt_pow_left₀ (by norm_num [H₁, H₂]) (by norm_num [H₁]) (by omega)

theorem negative_determinant_ne_zero (m : ℕ) :
    H₂ ^ (m + 2) - H₁ ^ (m + 2) ≠ 0 := by
  exact sub_ne_zero.mpr (ne_of_gt (twist_pow_lt (m + 2) (by omega)))

theorem positive_determinant_ne_zero (m : ℕ) (hm : 0 < m) :
    (H₂ ^ m)⁻¹ - (H₁ ^ m)⁻¹ ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hpow := congrArg (fun z : ℚ => z⁻¹) h
  simp only [inv_inv] at hpow
  exact (ne_of_gt (twist_pow_lt m hm)) hpow

end TachikawaCharZero
