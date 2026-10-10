import TachikawaCharZero.DeltaMatrices
import TachikawaCharZero.SignedDownHom

/-! Retaining the cone parity multiplies the two-branch determinant by
a nonzero sign. This proves the matrix certificate in every integer degree;
identifying the actual cone connecting map with it remains a separate step. -/
namespace TachikawaCharZero.SignedDeltaMatrices

def positive (a : ℤ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(H₁^m)⁻¹, -SignedDownHom.sign (k:=ℚ) a;
     (H₂^m)⁻¹, -SignedDownHom.sign (k:=ℚ) a]
def negative (a : ℤ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![H₁^(m+2), -SignedDownHom.sign (k:=ℚ) a;
     H₂^(m+2), -SignedDownHom.sign (k:=ℚ) a]

theorem sign_ne_zero (a : ℤ) : SignedDownHom.sign (k:=ℚ) a ≠ 0 :=
  zpow_ne_zero a (by norm_num)

theorem positive_det (a : ℤ) (m : ℕ) :
    (positive a m).det = SignedDownHom.sign (k:=ℚ) a * (positiveMatrix m).det := by
  rw [Matrix.det_fin_two,positiveMatrix_det]
  simp [positive]
  ring

theorem negative_det (a : ℤ) (m : ℕ) :
    (negative a m).det = SignedDownHom.sign (k:=ℚ) a * (negativeMatrix m).det := by
  rw [Matrix.det_fin_two,negativeMatrix_det]
  simp [negative]
  ring

theorem positive_det_ne_zero (a : ℤ) (m : ℕ) (hm : 0 < m) :
    (positive a m).det ≠ 0 := by
  rw [positive_det]
  exact mul_ne_zero (sign_ne_zero a) (positiveMatrix_det_ne_zero m hm)

theorem negative_det_ne_zero (a : ℤ) (m : ℕ) : (negative a m).det ≠ 0 := by
  rw [negative_det]
  exact mul_ne_zero (sign_ne_zero a) (negativeMatrix_det_ne_zero m)

theorem positive_isUnit (a : ℤ) (m : ℕ) (hm : 0 < m) : IsUnit (positive a m) := by
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  exact positive_det_ne_zero a m hm

theorem negative_isUnit (a : ℤ) (m : ℕ) : IsUnit (negative a m) := by
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  exact negative_det_ne_zero a m

theorem first_negative_det (a : ℤ) :
    (negative a 0).det = 5 * SignedDownHom.sign (k:=ℚ) a := by
  rw [negative_det,first_negativeMatrix_det,mul_comm]

end TachikawaCharZero.SignedDeltaMatrices
