import TachikawaCharZero.Resolution
import Mathlib.Algebra.Module.Projective

/-! Projective principal corners and the module-level form of the exact
coordinate recurrence. The generic corner argument follows OpenAI Math's
Tachikawa/Corner.lean, fixed at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
namespace TachikawaCharZero.Corner

variable {R : Type*} [Ring R]

def leftCorner (p : R) : Submodule R R where
  carrier := {a | a*p=a}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; change (a+b)*p=a+b; rw [add_mul, ha, hb]
  smul_mem' := by intro a b hb; change (a*b)*p=a*b; rw [mul_assoc, hb]

@[simp] theorem mem_leftCorner (p a : R) : a ∈ leftCorner p ↔ a*p=a := Iff.rfl

def projection {p : R} (hp : p*p=p) : R →ₗ[R] leftCorner p :=
  (LinearMap.mulRight R p).codRestrict (leftCorner p) (fun a => by
    change (a*p)*p=a*p
    rw [mul_assoc, hp])

theorem projective {p : R} (hp : p*p=p) : Module.Projective R (leftCorner p) := by
  apply Module.Projective.of_split (leftCorner p).subtype (projection hp)
  ext a
  exact a.property

def mulRight {p r : R} (b : R) (hb : b*r=b) : leftCorner p →ₗ[R] leftCorner r where
  toFun a := ⟨(a : R)*b, by change ((a:R)*b)*r=(a:R)*b; rw [mul_assoc, hb]⟩
  map_add' a c := Subtype.ext (add_mul _ _ _)
  map_smul' a c := Subtype.ext (mul_assoc _ _ _)

end TachikawaCharZero.Corner

namespace TachikawaCharZero.Resolution
open OAI.ArExplicit

abbrev A := C (2 : ℚ)
def vertexE : A := BaseAlgebra.basisVector 2 .e
abbrev Ce := Corner.leftCorner vertexE

theorem vertexE_idempotent : vertexE*vertexE=vertexE := by
  exact BaseAlgebra.basis_mul 2 .e .e

instance ceProjective : Module.Projective A Ce := Corner.projective vertexE_idempotent

theorem ceEmbed_mem (a : V) : ceEmbed a ∈ Corner.leftCorner vertexE := by
  ext i
  cases i <;> simp [ceEmbed, vertexE, BaseAlgebra.product]

def ceIso : V ≃ₗ[ℚ] Ce where
  toFun a := ⟨ceEmbed a, ceEmbed_mem a⟩
  invFun a := ![(a:A).coeff .e, (a:A).coeff .x, (a:A).coeff .y,
    (a:A).coeff .z, (a:A).coeff .t, (a:A).coeff .j]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    have h := a.property
    ext i
    cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · simpa [vertexE, BaseAlgebra.product, ceEmbed] using
        congrArg (fun c : A => c.coeff .u) h
    · simpa [vertexE, BaseAlgebra.product, ceEmbed] using
        congrArg (fun c : A => c.coeff .v) h
    · rfl
    · rfl
    · simpa [vertexE, BaseAlgebra.product, ceEmbed] using
        congrArg (fun c : A => c.coeff .f) h
    · simpa [vertexE, BaseAlgebra.product, ceEmbed] using
        congrArg (fun c : A => c.coeff .n) h
  map_add' a b := by
    apply Subtype.ext
    change ceEmbed (a+b) = ceEmbed a + ceEmbed b
    ext i
    cases i <;> simp [ceEmbed]
  map_smul' c a := by
    apply Subtype.ext
    change ceEmbed (c • a) = c • ceEmbed a
    ext i
    cases i <;> simp [ceEmbed]

theorem ell_mem (t : ℚ) : ell t * vertexE = ell t := by
  ext i
  cases i <;> simp [ell, vertexE, BaseAlgebra.product]

def ceDiff (t : ℚ) : Ce →ₗ[A] Ce := Corner.mulRight (ell t) (ell_mem t)

theorem ceDiff_iso (t : ℚ) (a : V) : ceDiff t (ceIso a) = ceIso (rightD t a) := by
  apply Subtype.ext
  exact (ceEmbed_rightD t a).symm

theorem ceDiff_exact_all_degrees (m : ℕ) :
    Function.Exact (ceDiff ((-2:ℚ)^(m+1))) (ceDiff ((-2:ℚ)^m)) := by
  intro a
  obtain ⟨a, rfl⟩ := ceIso.surjective a
  change ceDiff ((-2:ℚ)^m) (ceIso a) = 0 ↔
    ∃ b : Ce, ceDiff ((-2:ℚ)^(m+1)) b = ceIso a
  have hker : ceDiff ((-2:ℚ)^m) (ceIso a) = 0 ↔ rightD ((-2:ℚ)^m) a = 0 := by
    rw [ceDiff_iso, ← ceIso.map_zero]
    exact ceIso.injective.eq_iff
  have him : (∃ b : Ce, ceDiff ((-2:ℚ)^(m+1)) b = ceIso a) ↔
      ∃ b : V, rightD ((-2:ℚ)^(m+1)) b = a := by
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨b, rfl⟩ := ceIso.surjective b
      refine ⟨b, ceIso.injective ?_⟩
      simpa only [ceDiff_iso] using hb
    · rintro ⟨b, hb⟩
      exact ⟨ceIso b, by rw [ceDiff_iso, hb]⟩
  rw [hker, him]
  exact right_exact_all_degrees m a

end TachikawaCharZero.Resolution
