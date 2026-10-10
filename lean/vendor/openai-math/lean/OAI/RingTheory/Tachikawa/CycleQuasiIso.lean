import OAI.RingTheory.Tachikawa.Coresolution
import Mathlib.Algebra.Homology.ShortComplex.QuasiIso

/-! Characteristic-independent excerpt from OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [Ring R]

lemma shortComplex_quasiIso_of_cycles {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x-y) :
    ShortComplex.QuasiIso φ := by
  let f : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      change T.g (φ.τ₂ x.val) = 0
      rw [← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply, x.property, map_zero])
  have hf : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap f := by
    rintro x ⟨a,rfl⟩
    refine ⟨φ.τ₁ a, ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : S.X₁ ⟶ T.X₂ => t a) φ.comm₁₂
  let fq := Submodule.mapQ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) f hf
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
      T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom f
    φH := ModuleCat.ofHom fq
    commi := rfl
    commf' := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (congrArg (fun t : S.X₁ ⟶ T.X₂ => t x) φ.comm₁₂).symm
    commπ := rfl }
  rw [γ.quasiIso_iff]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (f x) = 0 at hx
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    have hz' : T.f z = φ.τ₂ x.val := congrArg Subtype.val hz
    obtain ⟨a,ha⟩ := hinj x.val x.property ⟨z,hz'⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨a, Subtype.ext ha⟩
  · intro y
    obtain ⟨y,rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x,hx,z,hz⟩ := hsurj y.val y.property
    refine ⟨Submodule.Quotient.mk ⟨x,hx⟩, ?_⟩
    change Submodule.Quotient.mk (f ⟨x,hx⟩) = Submodule.Quotient.mk y
    apply (Submodule.Quotient.eq _).mpr
    exact ⟨z, Subtype.ext hz⟩

lemma shortComplex_cycles_of_quasiIso {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hφ : ShortComplex.QuasiIso φ) :
    (∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) ∧
    (∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x-y) := by
  let f : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      change T.g (φ.τ₂ x.val) = 0
      rw [← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply, x.property, map_zero])
  have hf : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap f := by
    rintro x ⟨a,rfl⟩
    refine ⟨φ.τ₁ a, ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : S.X₁ ⟶ T.X₂ => t a) φ.comm₁₂
  let fq := Submodule.mapQ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) f hf
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
      T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom f
    φH := ModuleCat.ofHom fq
    commi := rfl
    commf' := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (congrArg (fun t : S.X₁ ⟶ T.X₂ => t x) φ.comm₁₂).symm
    commπ := rfl }
  have hbij : Function.Bijective fq := by
    have : IsIso γ.φH := γ.quasiIso_iff.mp hφ
    exact (ConcreteCategory.isIso_iff_bijective γ.φH).mp this
  constructor
  · intro x hx hbd
    have hz : fq (Submodule.Quotient.mk (⟨x,hx⟩ : LinearMap.ker S.g.hom)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      obtain ⟨z,hz⟩ := hbd
      exact ⟨z, Subtype.ext hz⟩
    have hz' := hbij.1 (hz.trans (map_zero fq).symm)
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz'
    exact ⟨z, congrArg Subtype.val hz⟩
  · intro y hy
    obtain ⟨x,hx⟩ := hbij.2 (Submodule.Quotient.mk (⟨y,hy⟩ : LinearMap.ker T.g.hom))
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (f x) = Submodule.Quotient.mk ⟨y,hy⟩ at hx
    obtain ⟨z,hz⟩ := (Submodule.Quotient.eq _).mp hx
    exact ⟨x.val, x.property, z, congrArg Subtype.val hz⟩
end Tachikawa
end
end OAI
