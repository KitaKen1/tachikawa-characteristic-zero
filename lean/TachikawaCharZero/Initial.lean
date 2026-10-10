import TachikawaCharZero.Corner
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The first differential and the quotient complete the exact sequence
of projective C-modules. CategoryTheory packaging is in ProjectivePackaging.
Simple.lean identifies this quotient with the one-dimensional character at f. -/
namespace TachikawaCharZero.Resolution
open OAI.ArExplicit

abbrev V₀ := Fin 4 → ℚ

def vertexF : A := BaseAlgebra.basisVector 2 .f
abbrev Cf := Corner.leftCorner vertexF

theorem vertexF_idempotent : vertexF*vertexF=vertexF := by
  exact BaseAlgebra.basis_mul 2 .f .f

instance cfProjective : Module.Projective A Cf := Corner.projective vertexF_idempotent

def cfEmbed (a : V₀) : A := ⟨fun
  | .f => a 0 | .u => a 1 | .v => a 2 | .n => a 3 | _ => 0⟩

theorem cfEmbed_mem (a : V₀) : cfEmbed a ∈ Corner.leftCorner vertexF := by
  ext i
  cases i <;> simp [cfEmbed, vertexF, BaseAlgebra.product]

def cfIso : V₀ ≃ₗ[ℚ] Cf where
  toFun a := ⟨cfEmbed a, cfEmbed_mem a⟩
  invFun a := ![(a:A).coeff .f, (a:A).coeff .u, (a:A).coeff .v, (a:A).coeff .n]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    change cfEmbed ![(a:A).coeff .f, (a:A).coeff .u, (a:A).coeff .v, (a:A).coeff .n] = (a:A)
    calc
      _ = (a:A)*vertexF := by ext i; cases i <;> simp [cfEmbed, vertexF, BaseAlgebra.product]
      _ = _ := a.property
  map_add' a b := by
    apply Subtype.ext
    change cfEmbed (a+b) = cfEmbed a + cfEmbed b
    ext i
    cases i <;> simp [cfEmbed]
  map_smul' c a := by
    apply Subtype.ext
    change cfEmbed (c • a) = c • cfEmbed a
    ext i
    cases i <;> simp [cfEmbed]

def initialD (a : V) : V₀ := ![0, a 0, a 1+a 2, 3*a 4]

theorem initial_kernel_iff (a : V) :
    initialD a = 0 ↔ ∃ b : W, a = imageEmbed 1 b := by
  constructor
  · intro h
    have h0 : a 0 = 0 := by have h' := congrFun h 1; simpa [initialD] using h'
    have h2 : a 2 = -a 1 := by
      have h' := congrFun h 2
      simp [initialD] at h'
      linarith
    have h4 : a 4 = 0 := by have h' := congrFun h 3; simpa [initialD] using h'
    refine ⟨![a 1, a 3, a 5], ?_⟩
    ext i
    fin_cases i <;> simp [imageEmbed, h0, h2, h4]
  · rintro ⟨b, rfl⟩
    ext i
    fin_cases i <;> simp [initialD, imageEmbed]

theorem initial_exact_coordinates : Function.Exact (rightD 1) initialD := by
  intro a
  constructor
  · intro h
    obtain ⟨b, rfl⟩ := (initial_kernel_iff a).mp h
    exact ⟨imagePreimage 1 b, rightD_preimage 1 (by norm_num) b⟩
  · rintro ⟨b, rfl⟩
    ext i
    fin_cases i <;> simp [initialD, rightD]

theorem cfEmbed_initialD (a : V) :
    cfEmbed (initialD a) = ceEmbed a * BaseAlgebra.basisVector 2 .u := by
  ext i
  cases i <;> norm_num [cfEmbed, ceEmbed, initialD, BaseAlgebra.product]

theorem u_fixed_by_f : BaseAlgebra.basisVector (2:ℚ) .u * vertexF =
    BaseAlgebra.basisVector (2:ℚ) .u := by
  exact BaseAlgebra.basis_mul 2 .u .f

def initialMap : Ce →ₗ[A] Cf := Corner.mulRight
  (BaseAlgebra.basisVector 2 .u) u_fixed_by_f

theorem initialMap_iso (a : V) : initialMap (ceIso a) = cfIso (initialD a) := by
  apply Subtype.ext
  exact (cfEmbed_initialD a).symm

theorem initial_exact : Function.Exact (ceDiff 1) initialMap := by
  intro a
  obtain ⟨a, rfl⟩ := ceIso.surjective a
  change initialMap (ceIso a)=0 ↔ ∃ b : Ce, ceDiff 1 b = ceIso a
  have hker : initialMap (ceIso a)=0 ↔ initialD a=0 := by
    rw [initialMap_iso, ← cfIso.map_zero]
    exact cfIso.injective.eq_iff
  have him : (∃ b : Ce, ceDiff 1 b = ceIso a) ↔ ∃ b : V, rightD 1 b = a := by
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨b, rfl⟩ := ceIso.surjective b
      exact ⟨b, ceIso.injective (by simpa only [ceDiff_iso] using hb)⟩
    · rintro ⟨b, hb⟩
      exact ⟨ceIso b, by rw [ceDiff_iso, hb]⟩
  rw [hker, him]
  exact initial_exact_coordinates a

abbrev Simple := Cf ⧸ LinearMap.range initialMap

def augmentation : Cf →ₗ[A] Simple := (LinearMap.range initialMap).mkQ

theorem augmentation_surjective : Function.Surjective augmentation :=
  Submodule.mkQ_surjective _

theorem augmentation_exact : Function.Exact initialMap augmentation := by
  intro a
  change (LinearMap.range initialMap).mkQ a = 0 ↔ a ∈ Set.range initialMap
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  rfl

instance ceFiniteQ : Module.Finite ℚ Ce := Module.Finite.equiv ceIso
instance cfFiniteQ : Module.Finite ℚ Cf := Module.Finite.equiv cfIso
instance ceFiniteA : Module.Finite A Ce := Module.Finite.of_restrictScalars_finite ℚ A Ce
instance cfFiniteA : Module.Finite A Cf := Module.Finite.of_restrictScalars_finite ℚ A Cf
instance simpleFiniteA : Module.Finite A Simple := inferInstance

end TachikawaCharZero.Resolution
