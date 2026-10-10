import OAI.Algebra.AuslanderReiten.Algebras.BaseAlgebra
import Mathlib.Algebra.Algebra.Equiv

/-! The signed automorphism of the ten-dimensional algebra. The construction
works over every commutative ring; characteristic zero is a specialization. -/
namespace TachikawaCharZero

open OAI.ArExplicit OAI.ArExplicit.Letter

variable {k : Type*} [CommRing k] (q : k)

abbrev C := BaseAlgebra k q

def signCoeff : Letter → k
  | .x | .y | .v | .t | .n => -1
  | _ => 1

def signed (a : C q) : C q := ⟨fun i => signCoeff i * a.coeff i⟩

@[simp] theorem signed_coeff (a : C q) (i : Letter) :
    (signed q a).coeff i = signCoeff i * a.coeff i := rfl

@[simp] theorem signed_signed (a : C q) : signed q (signed q a) = a := by
  ext i
  cases i <;> simp [signCoeff]

@[simp] theorem signed_add (a b : C q) :
    signed q (a + b) = signed q a + signed q b := by
  ext i
  simp [mul_add]

@[simp] theorem signed_smul (r : k) (a : C q) :
    signed q (r • a) = r • signed q a := by
  ext i
  simp only [signed_coeff, BaseAlgebra.coeff_smul]
  ring

@[simp] theorem signed_one : signed q (1 : C q) = 1 := by
  ext i
  cases i <;> simp [signCoeff]

@[simp] theorem signed_mul (a b : C q) :
    signed q (a * b) = signed q a * signed q b := by
  ext i
  cases i <;> simp [BaseAlgebra.product, signCoeff] <;> ring

def signedLinearEquiv : C q ≃ₗ[k] C q where
  toFun := signed q
  invFun := signed q
  left_inv := signed_signed q
  right_inv := signed_signed q
  map_add' := signed_add q
  map_smul' := signed_smul q

def sigma : C q ≃ₐ[k] C q :=
  AlgEquiv.ofLinearEquiv (signedLinearEquiv q) (signed_one q) (signed_mul q)

@[simp] theorem sigma_apply (a : C q) : sigma q a = signed q a := rfl

@[simp] theorem sigma_basis (i : Letter) :
    sigma q (BaseAlgebra.basisVector q i) =
      signCoeff (k := k) i • BaseAlgebra.basisVector q i := by
  ext l
  by_cases h : l = i
  · subst l; simp
  · simp [h]

@[simp] theorem sigma_involutive : Function.Involutive (sigma q) :=
  signed_signed q

end TachikawaCharZero
