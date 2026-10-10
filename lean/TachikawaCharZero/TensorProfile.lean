import TachikawaCharZero.TensorExt
import TachikawaCharZero.InducedSymmetry

/-! Ordinary self-Ext of the one-dimensional character over E=T⊗T.
Finite free resolutions feed the signed Künneth theorem. Only the supported
diagonal summands survive; they are indexed by Fin (m+1) in degree 3m.
This proves the vector-space profile, not the Yoneda interchange law or
negative Tate groups. -/
namespace TachikawaCharZero.TensorProfile
noncomputable section
open CategoryTheory CategoryTheory.Abelian Induced OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

abbrev E := T ⊗[ℚ] T
abbrev X₂ := ((OuterTensor.bifunctor ℚ T T).obj X).obj X

def simpleFinite : FiniteModule ℚ T where
  obj := X
  finite := Module.Finite.of_restrictScalars_finite ℚ T S

abbrev P := simpleFinite.projectiveResolution

def kunneth (n : ℕ) : Ext X₂ X₂ n ≃ₗ[ℚ]
    (∀ t : SignedTotalPairing.Diag n, Ext X X t.val.1 ⊗[ℚ] Ext X X t.val.2) :=
  TensorExt.extKunneth P P n

abbrev Factor (n : ℕ) (t : SignedTotalPairing.Diag n) :=
  Ext X X t.val.1 ⊗[ℚ] Ext X X t.val.2

def Supported (n : ℕ) (t : SignedTotalPairing.Diag n) : Prop :=
  t.val.1%3=0 ∧ t.val.2%3=0
instance (n : ℕ) : DecidablePred (Supported n) := fun t => inferInstanceAs
  (Decidable (t.val.1%3=0 ∧ t.val.2%3=0))

theorem factor_zero (n : ℕ) (t : SignedTotalPairing.Diag n) (h : ¬ Supported n t) :
    Subsingleton (Factor n t) := by
  by_cases h₁ : t.val.1%3=0
  · have h₂ : t.val.2%3≠0 := fun h₂ => h ⟨h₁,h₂⟩
    let := self_ext_off_multiples t.val.2 h₂
    infer_instance
  · let := self_ext_off_multiples t.val.1 h₁
    infer_instance

theorem self_ext_off_multiples (n : ℕ) (hn : n%3≠0) : Subsingleton (Ext X₂ X₂ n) := by
  have (t : SignedTotalPairing.Diag n) : Subsingleton (Factor n t) :=
    factor_zero n t (by
      rintro ⟨h₁,h₂⟩
      have ht := t.property
      change t.val.1+t.val.2=n at ht
      omega)
  exact (kunneth n).injective.subsingleton

/-- Restrict a family to its nonzero support, with zero extension as inverse. -/
def piSupportedEquiv {ι : Type*} (p : ι → Prop) [DecidablePred p]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]
    (hzero : ∀ i, ¬ p i → Subsingleton (M i)) :
    (∀ i, M i) ≃ₗ[ℚ] (∀ i : {j // p j}, M i.val) where
  toFun f i := f i.val
  invFun f i := if h : p i then f ⟨i,h⟩ else 0
  left_inv f := by
    funext i
    by_cases hi : p i
    · simp only [dite_eq_left hi]
    · simp only [dite_eq_right hi]
      exact (hzero i hi).elim _ _
  right_inv f := by funext i; simp only [dite_eq_left i.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev Support (n : ℕ) := {t : SignedTotalPairing.Diag n // Supported n t}

def supportedEquiv (m : ℕ) : Support (3*m) ≃ Fin (m+1) where
  toFun t := ⟨t.val.val.1/3,by
    have ht := t.val.property
    have h₁ := t.property.1
    change t.val.val.1+t.val.val.2=3*m at ht
    omega⟩
  invFun i := ⟨⟨(3*i.val,3*(m-i.val)),by have hi := i.isLt; change 3*i.val+3*(m-i.val)=3*m; omega⟩,
    by
      change (3*i.val)%3=0 ∧ (3*(m-i.val))%3=0
      constructor <;> omega⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have h₁ := t.property.1; dsimp; omega
    · have h₁ := t.property.1
      have h₂ := t.property.2
      have ht := t.val.property
      change t.val.val.1+t.val.val.2=3*m at ht
      dsimp
      omega
  right_inv i := by apply Fin.ext; dsimp; omega

def factorEquiv (n : ℕ) (hn : n%3=0) : Ext X X n ≃ₗ[ℚ] ℚ := by
  rw [show n=3*(n/3) by omega]
  exact extMultiple (n/3)

def supportedFactorEquiv (n : ℕ) (t : Support n) : Factor n t.val ≃ₗ[ℚ] ℚ :=
  (TensorProduct.congr (factorEquiv t.val.val.1 t.property.1)
    (factorEquiv t.val.val.2 t.property.2)).trans (TensorProduct.lid ℚ ℚ)

def extMultiple (m : ℕ) : Ext X₂ X₂ (3*m) ≃ₗ[ℚ] (Fin (m+1) → ℚ) :=
  (kunneth (3*m)).trans
    ((piSupportedEquiv (Supported (3*m)) (Factor (3*m)) (factor_zero (3*m))).trans
      ((LinearEquiv.piCongrRight (supportedFactorEquiv (3*m))).trans
        (LinearEquiv.funCongrLeft ℚ ℚ (supportedEquiv m).symm)))

theorem ext_multiple_finrank (m : ℕ) : Module.finrank ℚ (Ext X₂ X₂ (3*m))=m+1 := by
  rw [(extMultiple m).finrank_eq]
  simp

/-- Keep the bundled scalar action visible to typeclass inference. -/
def sCanon : ModuleCat T := X

def simpleGroundEquiv : sCanon ≃ₗ[ℚ] ℚ where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change characterT (algebraMap ℚ T r)*(show ℚ from x)=r*(show ℚ from x)
    rw [AlgHom.commutes]
    simp

def groundEquiv : X₂ ≃ₗ[ℚ] ℚ :=
  (OuterTensor.underlyingEquiv X X).trans
    ((TensorProduct.congr simpleGroundEquiv simpleGroundEquiv).trans (TensorProduct.lid ℚ ℚ))

instance finiteQ : Module.Finite ℚ X₂ := Module.Finite.of_injective
  groundEquiv.toLinearMap groundEquiv.injective

theorem finrank_one : Module.finrank ℚ X₂=1 := by
  rw [groundEquiv.finrank_eq]
  exact Module.finrank_self ℚ

instance simple : IsSimpleModule E X₂ :=
  (isSimpleModule_iff E X₂).mpr (is_simple_module_of_finrank_eq_one (A := E) finrank_one)

theorem not_projective : ¬ Module.Projective E X₂ := by
  intro h
  let := h
  let : Subsingleton (Ext X₂ X₂ 3) := Ext.subsingleton_of_projective _ _ 2
  have hf := ext_multiple_finrank 1
  rw [Module.finrank_zero_of_subsingleton] at hf
  norm_num at hf

theorem E_symmetric : OAI.Tachikawa.SymmetricOver ℚ E := Starting.E_symmetric
theorem E_injective : Module.Injective E E := Starting.E_injective
theorem E_finrank : Module.finrank ℚ E=400 := Starting.E_finrank

end
end TachikawaCharZero.TensorProfile
