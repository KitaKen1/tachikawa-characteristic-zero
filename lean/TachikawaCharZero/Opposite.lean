import TachikawaCharZero.Corner
import Mathlib.Algebra.Algebra.Opposite

/-! A rational anti-involution identifies C with its opposite algebra.
This permits transporting left resolutions instead of repeating right-side
coordinate calculations. The coefficients are an explicit witness, not a search. -/
namespace TachikawaCharZero.Resolution
open OAI.ArExplicit

def reverse (a : A) : A := ⟨fun
  | .e => a.coeff .e | .f => a.coeff .f
  | .x => 2*a.coeff .y | .y => (1/2)*a.coeff .x
  | .z => a.coeff .z | .n => a.coeff .n
  | .u => a.coeff .t | .t => a.coeff .u
  | .v => (1/2)*a.coeff .j | .j => 2*a.coeff .v⟩

theorem reverse_reverse (a : A) : reverse (reverse a) = a := by
  ext i
  cases i <;> simp [reverse]

theorem reverse_add (a b : A) : reverse (a+b)=reverse a+reverse b := by
  ext i
  cases i <;> simp [reverse]
  all_goals ring

theorem reverse_smul (c : ℚ) (a : A) : reverse (c • a)=c • reverse a := by
  ext i
  cases i <;> simp [reverse]
  all_goals ring

theorem reverse_mul (a b : A) : reverse (a*b)=reverse b*reverse a := by
  ext i
  cases i <;> simp [reverse,BaseAlgebra.product]
  all_goals ring

theorem reverse_one : reverse (1:A)=1 := by
  ext i
  cases i <;> norm_num [reverse]

def oppositeIso : A ≃ₐ[ℚ] Aᵐᵒᵖ where
  toFun a := MulOpposite.op (reverse a)
  invFun a := reverse a.unop
  left_inv := reverse_reverse
  right_inv a := by apply MulOpposite.unop_injective; exact reverse_reverse a.unop
  map_add' a b := congrArg MulOpposite.op (reverse_add a b)
  map_mul' a b := congrArg MulOpposite.op (reverse_mul a b)
  commutes' c := by
    apply MulOpposite.unop_injective
    change reverse (algebraMap ℚ A c)=algebraMap ℚ A c
    rw [Algebra.algebraMap_eq_smul_one,reverse_smul,reverse_one]

end TachikawaCharZero.Resolution
