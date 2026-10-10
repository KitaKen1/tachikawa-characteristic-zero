import TachikawaCharZero.Parameters
import TachikawaCharZero.SignedAutomorphism
import Mathlib.Tactic

/-! Exactness in all degrees for the coordinate complex underlying the
simple C-module resolution. Corner.lean and ProjectivePackaging.lean supply
the C-module/projectivity bridge. -/
namespace TachikawaCharZero.Resolution

open OAI.ArExplicit

abbrev V := Fin 6 → ℚ
abbrev W := Fin 3 → ℚ

def ceEmbed (a : V) : C (2 : ℚ) := ⟨fun
  | .e => a 0 | .x => a 1 | .y => a 2 | .z => a 3
  | .t => a 4 | .j => a 5 | _ => 0⟩

def ell (t : ℚ) : C (2 : ℚ) :=
  BaseAlgebra.basisVector 2 .x + (-t) • BaseAlgebra.basisVector 2 .y

def rightD (t : ℚ) (a : V) : V :=
  ![0, a 0, -t * a 0, -2 * t * a 1 + a 2, 0, (1 - 4 * t) * a 4]

def kernelEmbed (t : ℚ) (b : W) : V := ![0, b 0, 2 * t * b 0, b 1, 0, b 2]
def imageEmbed (t : ℚ) (b : W) : V := ![0, b 0, -t * b 0, b 1, 0, b 2]
def imagePreimage (t : ℚ) (b : W) : V := ![b 0, 0, b 1, 0, b 2 / (1 - 4*t), 0]

theorem ceEmbed_injective : Function.Injective ceEmbed := by
  intro a b h
  ext i
  fin_cases i
  · exact congrArg (fun c : C (2 : ℚ) => c.coeff .e) h
  · exact congrArg (fun c : C (2 : ℚ) => c.coeff .x) h
  · exact congrArg (fun c : C (2 : ℚ) => c.coeff .y) h
  · exact congrArg (fun c : C (2 : ℚ) => c.coeff .z) h
  · exact congrArg (fun c : C (2 : ℚ) => c.coeff .t) h
  · exact congrArg (fun c : C (2 : ℚ) => c.coeff .j) h

theorem ceEmbed_rightD (t : ℚ) (a : V) :
    ceEmbed (rightD t a) = ceEmbed a * ell t := by
  ext i
  cases i <;> simp [ceEmbed, rightD, ell, BaseAlgebra.product] <;> ring

def rightLinear (t : ℚ) : V →ₗ[ℚ] V where
  toFun := rightD t
  map_add' a b := by ext i; fin_cases i <;> simp [rightD] <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp [rightD] <;> ring

theorem consecutive_zero (t : ℚ) (a : V) : rightD t (rightD (-2*t) a) = 0 := by
  ext i
  fin_cases i <;> simp [rightD]

theorem kernel_iff (t : ℚ) (ht : 1 - 4*t ≠ 0) (a : V) :
    rightD t a = 0 ↔ ∃ b : W, a = kernelEmbed t b := by
  constructor
  · intro h
    have h0 : a 0 = 0 := by have h' := congrFun h 1; simpa [rightD] using h'
    have h2 : a 2 = 2*t*a 1 := by
      have h' := congrFun h 3
      simp [rightD] at h'
      linarith
    have h4 : a 4 = 0 := by
      have h' := congrFun h 5
      have hmul : (1-4*t)*a 4 = 0 := by simpa [rightD] using h'
      exact (mul_eq_zero.mp hmul).resolve_left ht
    refine ⟨![a 1, a 3, a 5], ?_⟩
    ext i
    fin_cases i <;> simp [kernelEmbed, h0, h2, h4]
  · rintro ⟨b, rfl⟩
    ext i
    fin_cases i <;> simp [rightD, kernelEmbed]

theorem rightD_preimage (t : ℚ) (ht : 1-4*t ≠ 0) (b : W) :
    rightD t (imagePreimage t b) = imageEmbed t b := by
  ext i
  fin_cases i <;> simp [rightD, imagePreimage, imageEmbed]
  field_simp [ht]

theorem next_image_eq_kernel (t : ℚ) (b : W) :
    imageEmbed (-2*t) b = kernelEmbed t b := by
  ext i
  fin_cases i <;> simp [imageEmbed, kernelEmbed]

theorem right_exact_all_degrees (m : ℕ) :
    Function.Exact (rightD ((-2 : ℚ) ^ (m+1))) (rightD ((-2 : ℚ) ^ m)) := by
  intro a
  have hp : (-2 : ℚ) ^ (m+1) = -2 * (-2 : ℚ)^m := by rw [pow_succ]; ring
  constructor
  · intro h
    obtain ⟨b, rfl⟩ := (kernel_iff _ (resolution_right_coefficient_ne_zero m) a).mp h
    refine ⟨imagePreimage ((-2 : ℚ)^(m+1)) b, ?_⟩
    rw [rightD_preimage _ (resolution_right_coefficient_ne_zero (m+1)), hp,
      next_image_eq_kernel]
  · rintro ⟨b, rfl⟩
    rw [hp]
    exact consecutive_zero _ b

end TachikawaCharZero.Resolution
