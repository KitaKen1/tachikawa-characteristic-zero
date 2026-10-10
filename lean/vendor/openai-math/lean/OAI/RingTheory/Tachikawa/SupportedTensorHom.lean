import OAI.RingTheory.Tachikawa.IntegerTensorSupport

/-! Characteristic-independent excerpts from pinned OpenAI Math,
commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section


namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {I : Type} (F : I → ModuleCat R) (N : ModuleCat R)

def coproductHomEquiv : (∐ F ⟶ N) ≃ₗ[k] (∀ i, F i ⟶ N) where
  toFun f i := Sigma.ι F i ≫ f
  invFun f := Sigma.desc f
  left_inv f := Sigma.hom_ext _ _ (fun i => by simp)
  right_inv f := funext fun i => by simp
  map_add' f g := funext fun i => by simp only [Pi.add_apply, Preadditive.comp_add]
  map_smul' r f := funext fun i => by simp only [Pi.smul_apply, RingHom.id_apply, CategoryTheory.Linear.comp_smul]

end Tachikawa

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k]

def piSupportedEquiv {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (i₀ : ι) (hz : ∀ i, i ≠ i₀ → Subsingleton (V i)) :
    (∀ i, V i) ≃ₗ[k] V i₀ := by
  classical
  apply LinearEquiv.ofBijective (LinearMap.proj i₀)
  constructor
  · intro x y h
    funext i
    by_cases hi : i = i₀
    · subst i; exact h
    · exact (hz i hi).elim _ _
  · intro x
    refine ⟨Pi.single i₀ x, ?_⟩
    exact Pi.single_eq_same i₀ x

namespace OuterTensor
variable {A B : Type} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (P : ChainComplex (ModuleCat.{0} A) ℤ) (Q : ChainComplex (ModuleCat.{0} B) ℤ)
  (U : ModuleCat A) (V : ModuleCat B)

lemma hom_zero_left (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    (hz : ∀ f : M ⟶ U, f = 0)
    (f : ((bifunctor k A B).obj M |>.obj N) ⟶ ((bifunctor k A B).obj U |>.obj V)) : f = 0 := by
  let : Subsingleton (M ⟶ U) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  obtain ⟨x,rfl⟩ := homMap_surjective (k := k) M U N V f
  rw [Subsingleton.elim x 0, map_zero]

lemma hom_zero_right (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    (hz : ∀ f : N ⟶ V, f = 0)
    (f : ((bifunctor k A B).obj M |>.obj N) ⟶ ((bifunctor k A B).obj U |>.obj V)) : f = 0 := by
  let : Subsingleton (N ⟶ V) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  obtain ⟨x,rfl⟩ := homMap_surjective (k := k) M U N V f
  rw [Subsingleton.elim x 0, map_zero]

lemma total_hom_zero (a b n : ℤ) (hn : n ≠ a+b)
    (fP : ∀ i, Module.Finite A (P.X i)) (fQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i)) (pQ : ∀ j, Module.Projective B (Q.X j))
    (zP : ∀ i, i ≠ a → ∀ f : P.X i ⟶ U, f = 0)
    (zQ : ∀ j, j ≠ b → ∀ f : Q.X j ⟶ V, f = 0)
    (f : (mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n ⟶
      ((bifunctor k A B).obj U).obj V) : f = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  let := fP i
  let := fQ j
  let := pP i
  let := pQ j
  rw [comp_zero]
  by_cases hi : i = a
  · exact hom_zero_right U V (P.X i) (Q.X j) (zQ j (by dsimp at hij; omega)) _
  · exact hom_zero_left U V (P.X i) (Q.X j) (zP i hi) _

def totalHomSupported (a b : ℤ)
    (fP : ∀ i, Module.Finite A (P.X i)) (fQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i)) (pQ : ∀ j, Module.Projective B (Q.X j))
    (zP : ∀ i, i ≠ a → ∀ f : P.X i ⟶ U, f = 0)
    (zQ : ∀ j, j ≠ b → ∀ f : Q.X j ⟶ V, f = 0) :
    ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X (a+b) ⟶
      ((bifunctor k A B).obj U).obj V) ≃ₗ[k]
      (((bifunctor k A B).obj (P.X a)).obj (Q.X b) ⟶
      ((bifunctor k A B).obj U).obj V) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=a+b}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let W := ((bifunctor k A B).obj U).obj V
  change (∐ F ⟶ W) ≃ₗ[k] _
  refine (coproductHomEquiv F W).trans (piSupportedEquiv _ (⟨(a,b),rfl⟩ : I) ?_)
  intro ij hij
  let := fP ij.val.1
  let := fQ ij.val.2
  let := pP ij.val.1
  let := pQ ij.val.2
  have hz (f : F ij ⟶ W) : f = 0 := by
    by_cases h : ij.val.1 = a
    · apply hom_zero_right U V (P.X ij.val.1) (Q.X ij.val.2) _ f
      apply zQ
      intro h'
      apply hij
      exact Subtype.ext (Prod.ext h h')
    · exact hom_zero_left U V (P.X ij.val.1) (Q.X ij.val.2) (zP _ h) f
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

end OuterTensor
end Tachikawa

end
end OAI
