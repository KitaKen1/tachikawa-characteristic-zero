import TachikawaCharZero.PeriodThree

/-! The ordinary self-Ext profile over T in every nonnegative degree.
The period is Yoneda composition with the concrete nonzero degree-three
class. The generic composition and scalar-endomorphism proofs follow
OpenAI Math's Tachikawa/Period.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
No assertion about negative Tate degrees or the final counterexample is made. -/
namespace TachikawaCharZero.Induced
noncomputable section
open CategoryTheory CategoryTheory.Abelian Resolution
open scoped ModuleCat.Algebra

theorem period_apply (n : ℕ) (x : Ext X X n) :
    period n x=initial_shortExact.extClass.comp (c := n+3)
      (middle_shortExact.extClass.comp (c := n+2)
        (upper_shortExact.extClass.comp (c := n+1)
          ((Ext.mk₀ lowerShort.g).comp x (zero_add n)) (by omega)) (by omega)) (by omega) := rfl

theorem period_eq_tau_comp (n : ℕ) (x : Ext X X n) :
    period n x=tau.comp x (by omega) := by
  simp only [tau,period_apply,Ext.comp_mk₀_id]
  rw [Ext.comp_assoc (a₂₃ := n+2) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := n+1) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := n) _ _ _ (by omega) (by omega) (by omega)]

def endEquiv : (X ⟶ X) ≃ₗ[ℚ] ℚ where
  toFun f := f (show S from (1:ℚ))
  invFun r := r • 𝟙 X
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hf := f.hom.map_smul_of_tower (show ℚ from x) (show S from (1:ℚ))
    change f (show S from (show ℚ from x)*1)=
      (show ℚ from x)*(show ℚ from f (show S from (1:ℚ))) at hf
    change (show ℚ from f (show S from (1:ℚ)))*(show ℚ from x)=(show ℚ from f x)
    have hx : (show S from (show ℚ from x)*1)=x := mul_one (show ℚ from x)
    rw [hx] at hf
    exact (mul_comm _ _).trans hf.symm
  right_inv r := mul_one r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extZeroEquiv : Ext X X 0 ≃ₗ[ℚ] ℚ where
  toAddEquiv := Ext.addEquiv₀.trans endEquiv.toAddEquiv
  map_smul' r x := by
    obtain ⟨f,rfl⟩ := Ext.homEquiv₀.symm.surjective x
    change endEquiv (Ext.homEquiv₀ (r • Ext.mk₀ f))=
      r • endEquiv (Ext.homEquiv₀ (Ext.mk₀ f))
    rw [← Ext.mk₀_smul]
    have h0 (g : X ⟶ X) : Ext.homEquiv₀ (Ext.mk₀ g)=g := Ext.homEquiv₀.apply_symm_apply g
    rw [h0,h0]
    change (algebraMap ℚ T r) • (f (show S from (1:ℚ)))=r • (f (show S from (1:ℚ)))
    exact IsScalarTower.algebraMap_smul T r _

def extMultiple : (m : ℕ) → Ext X X (3*m) ≃ₗ[ℚ] ℚ
  | 0 => extZeroEquiv
  | m+1 => by
    rw [show 3*(m+1)=3*m+3 by omega]
    exact (period (3*m)).symm.trans (extMultiple m)

theorem self_ext_off_multiples (n : ℕ) (hn : n%3≠0) : Subsingleton (Ext X X n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n=1
    · subst n; exact self_ext_one_zero
    by_cases h2 : n=2
    · subst n; exact self_ext_two_zero
    have h3 : 3≤n := by omega
    have hm : (n-3)%3≠0 := by omega
    have := ih (n-3) (by omega) hm
    rw [show n=(n-3)+3 by omega]
    exact (period (n-3)).symm.injective.subsingleton

theorem ext_multiple_finrank (m : ℕ) : Module.finrank ℚ (Ext X X (3*m))=1 := by
  rw [(extMultiple m).finrank_eq]
  exact Module.finrank_self ℚ

theorem S_finrank : Module.finrank ℚ S=1 := Module.finrank_self ℚ
instance S_simple : IsSimpleModule T S :=
  (isSimpleModule_iff T S).mpr (is_simple_module_of_finrank_eq_one (A := T) S_finrank)

theorem TE_finrank : Module.finrank ℚ TE=12 := by
  rw [decompE.finrank_eq,Module.finrank_prod,Subspace.dual_finrank_eq,
    ← ceIso.finrank_eq,← ecIso.finrank_eq]
  norm_num [Module.finrank_pi]

theorem TF_finrank : Module.finrank ℚ TF=8 := by
  rw [decompF.finrank_eq,Module.finrank_prod,Subspace.dual_finrank_eq,
    ← cfIso.finrank_eq,← fcIso.finrank_eq]
  norm_num [Module.finrank_pi]

end
end TachikawaCharZero.Induced
