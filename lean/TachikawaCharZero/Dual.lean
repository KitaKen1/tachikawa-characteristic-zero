import TachikawaCharZero.Corner
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The rational dual bimodule. The actions are the standard dual actions,
adapted from OpenAI Math, Tachikawa/Symmetry.lean, at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Only the necessary imports are used here. -/
namespace TachikawaCharZero.Resolution

def Dual := Module.Dual ℚ A
instance : FunLike Dual A ℚ := inferInstanceAs (FunLike (Module.Dual ℚ A) A ℚ)
instance : LinearMapClass Dual ℚ A ℚ := inferInstanceAs (LinearMapClass (Module.Dual ℚ A) ℚ A ℚ)
instance : AddCommGroup Dual := inferInstanceAs (AddCommGroup (Module.Dual ℚ A))
instance : Module ℚ Dual := inferInstanceAs (Module ℚ (Module.Dual ℚ A))

@[ext] theorem dual_ext {φ ψ : Dual} (h : ∀ a, φ a = ψ a) : φ = ψ := LinearMap.ext h

@[simp] theorem dual_zero_apply (a : A) : (0:Dual) a = 0 := rfl
@[simp] theorem dual_add_apply (φ ψ : Dual) (a : A) : (φ+ψ) a = φ a + ψ a := rfl
@[simp] theorem dual_smul_apply (c : ℚ) (φ : Dual) (a : A) : (c • φ) a = c * φ a := rfl

instance dualLeft : Module A Dual where
  smul a φ := φ.comp (LinearMap.mulRight ℚ a)
  one_smul φ := by ext x; change φ (x*1)=φ x; simp
  mul_smul a b φ := by ext x; change φ (x*(a*b))=φ ((x*a)*b); simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by ext x; change φ (x*(a+b))=φ (x*a)+φ (x*b); simp [mul_add]
  zero_smul φ := by ext x; change φ (x*0)=0; simp

@[simp] theorem dual_left_apply (a : A) (φ : Dual) (x : A) : (a • φ) x = φ (x*a) := rfl

instance dualRight : Module Aᵐᵒᵖ Dual where
  smul a φ := φ.comp (LinearMap.mulLeft ℚ a.unop)
  one_smul φ := by ext x; change φ (1*x)=φ x; simp
  mul_smul a b φ := by
    ext x
    change φ ((b.unop*a.unop)*x)=φ (b.unop*(a.unop*x))
    simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by ext x; change φ ((a.unop+b.unop)*x)=φ (a.unop*x)+φ (b.unop*x); simp [add_mul]
  zero_smul φ := by ext x; change φ (0*x)=0; simp

@[simp] theorem dual_right_apply (a : Aᵐᵒᵖ) (φ : Dual) (x : A) : (a • φ) x = φ (a.unop*x) := rfl

instance : SMulCommClass A Aᵐᵒᵖ Dual where
  smul_comm a b φ := by ext x; simp [mul_assoc]

instance : IsScalarTower ℚ A Dual where
  smul_assoc c a φ := by ext x; simp

instance : IsScalarTower ℚ Aᵐᵒᵖ Dual where
  smul_assoc c a φ := by ext x; simp

instance : SMulCommClass ℚ A Dual where
  smul_comm c a φ := by ext x; simp

instance : SMulCommClass ℚ Aᵐᵒᵖ Dual where
  smul_comm c a φ := by ext x; simp

instance dualFiniteQ : Module.Finite ℚ Dual :=
  inferInstanceAs (Module.Finite ℚ (Module.Dual ℚ A))

end TachikawaCharZero.Resolution
