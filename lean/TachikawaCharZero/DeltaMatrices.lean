import TachikawaCharZero.Parameters
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-! The actual two-by-two comparison matrices are invertible in all supported
positive and negative degrees, including negative degree minus one. -/
namespace TachikawaCharZero

def positiveMatrix (m : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(H₁ ^ m)⁻¹, -1; (H₂ ^ m)⁻¹, -1]

def negativeMatrix (m : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![H₁ ^ (m+2), -1; H₂ ^ (m+2), -1]

theorem positiveMatrix_det (m : ℕ) :
    (positiveMatrix m).det = (H₂ ^ m)⁻¹ - (H₁ ^ m)⁻¹ := by
  rw [Matrix.det_fin_two]
  simp [positiveMatrix]
  ring

theorem negativeMatrix_det (m : ℕ) :
    (negativeMatrix m).det = H₂ ^ (m+2) - H₁ ^ (m+2) := by
  rw [Matrix.det_fin_two]
  simp [negativeMatrix]
  ring

theorem positiveMatrix_det_ne_zero (m : ℕ) (hm : 0 < m) :
    (positiveMatrix m).det ≠ 0 := by
  rw [positiveMatrix_det]
  exact positive_determinant_ne_zero m hm

theorem negativeMatrix_det_ne_zero (m : ℕ) : (negativeMatrix m).det ≠ 0 := by
  rw [negativeMatrix_det]
  exact negative_determinant_ne_zero m

theorem positiveMatrix_isUnit (m : ℕ) (hm : 0 < m) : IsUnit (positiveMatrix m) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact positiveMatrix_det_ne_zero m hm

theorem negativeMatrix_isUnit (m : ℕ) : IsUnit (negativeMatrix m) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact negativeMatrix_det_ne_zero m

theorem first_negativeMatrix_det : (negativeMatrix 0).det = 5 := by
  rw [negativeMatrix_det]
  norm_num [H₁, H₂]

end TachikawaCharZero
