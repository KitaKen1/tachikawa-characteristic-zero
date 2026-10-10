import TachikawaCharZero.Simple
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Algebra.Opposite

/-! Evaluation identifies Hom(Cp,C) with pC as a right module.
The generic argument is adapted from OpenAI Math's Tachikawa/Corner.lean,
fixed at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Only this generic API is reused; no characteristic-two construction is imported. -/
namespace TachikawaCharZero.Corner
variable {R : Type*} [Ring R]

def rightCorner (p : R) : Submodule Rᵐᵒᵖ R where
  carrier := {a | p*a=a}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; change p*(a+b)=a+b; rw [mul_add,ha,hb]
  smul_mem' := by intro a b hb; change p*(b*a.unop)=b*a.unop; rw [← mul_assoc,hb]

def leftGenerator {p : R} (hp : p*p=p) : leftCorner p := ⟨p,hp⟩

theorem left_hom_apply {p : R} (hp : p*p=p) (F : leftCorner p →ₗ[R] R)
    (a : leftCorner p) : F a = (a:R)*F (leftGenerator hp) := by
  have h : (a:R) • leftGenerator hp = a := Subtype.ext a.property
  calc
    F a = F ((a:R) • leftGenerator hp) := congrArg F h.symm
    _ = (a:R) • F (leftGenerator hp) := F.map_smul _ _
    _ = _ := rfl

def leftLift {p : R} (b : rightCorner p) : leftCorner p →ₗ[R] R where
  toFun a := (a:R)*(b:R)
  map_add' _ _ := add_mul _ _ _
  map_smul' _ _ := mul_assoc _ _ _

def homRightEquiv {p : R} (hp : p*p=p) :
    (leftCorner p →ₗ[R] R) ≃ₗ[Rᵐᵒᵖ] rightCorner p where
  toFun F := ⟨F (leftGenerator hp), by
    have h : p • leftGenerator hp = leftGenerator hp := Subtype.ext hp
    change p • F (leftGenerator hp) = F (leftGenerator hp)
    rw [← F.map_smul,h]⟩
  invFun := leftLift
  left_inv F := by apply LinearMap.ext; intro a; exact (left_hom_apply hp F a).symm
  right_inv b := Subtype.ext b.property
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mulLeft {p r : R} (b : R) (hb : r*b=b) :
    rightCorner p →ₗ[Rᵐᵒᵖ] rightCorner r where
  toFun a := ⟨b*(a:R), by change r*(b*(a:R))=b*(a:R); rw [← mul_assoc,hb]⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_assoc _ _ _).symm

theorem homRightEquiv_precomp {p r : R} (hp : p*p=p) (hr : r*r=r)
    (b : R) (hpb : p*b=b) (hbr : b*r=b) (F : leftCorner r →ₗ[R] R) :
    homRightEquiv hp (F.comp (mulRight b hbr)) =
      mulLeft b hpb (homRightEquiv hr F) := by
  apply Subtype.ext
  change F ⟨p*b,_⟩ = b*F (leftGenerator hr)
  rw [left_hom_apply hr F]
  change (p*b)*F (leftGenerator hr) = _
  rw [hpb]

end TachikawaCharZero.Corner

namespace TachikawaCharZero.Resolution
open OAI.ArExplicit
abbrev EC := Corner.rightCorner vertexE
abbrev FC := Corner.rightCorner vertexF

def ecEmbed (a : V) : A := ⟨fun
  | .e => a 0 | .x => a 1 | .y => a 2 | .z => a 3
  | .u => a 4 | .v => a 5 | _ => 0⟩

def fcEmbed (a : V₀) : A := ⟨fun
  | .f => a 0 | .t => a 1 | .j => a 2 | .n => a 3 | _ => 0⟩

def ecIso : V ≃ₗ[ℚ] EC where
  toFun a := ⟨ecEmbed a, by ext i; cases i <;> simp [ecEmbed,vertexE,BaseAlgebra.product]⟩
  invFun a := ![(a:A).coeff .e,(a:A).coeff .x,(a:A).coeff .y,
    (a:A).coeff .z,(a:A).coeff .u,(a:A).coeff .v]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    calc
      _ = vertexE*(a:A) := by ext i; cases i <;> simp [ecEmbed,vertexE,BaseAlgebra.product]
      _ = _ := a.property
  map_add' _ _ := by apply Subtype.ext; ext i; cases i <;> simp [ecEmbed]
  map_smul' _ _ := by apply Subtype.ext; ext i; cases i <;> simp [ecEmbed]

def fcIso : V₀ ≃ₗ[ℚ] FC where
  toFun a := ⟨fcEmbed a, by ext i; cases i <;> simp [fcEmbed,vertexF,BaseAlgebra.product]⟩
  invFun a := ![(a:A).coeff .f,(a:A).coeff .t,(a:A).coeff .j,(a:A).coeff .n]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    calc
      _ = vertexF*(a:A) := by ext i; cases i <;> simp [fcEmbed,vertexF,BaseAlgebra.product]
      _ = _ := a.property
  map_add' _ _ := by apply Subtype.ext; ext i; cases i <;> simp [fcEmbed]
  map_smul' _ _ := by apply Subtype.ext; ext i; cases i <;> simp [fcEmbed]

end TachikawaCharZero.Resolution
