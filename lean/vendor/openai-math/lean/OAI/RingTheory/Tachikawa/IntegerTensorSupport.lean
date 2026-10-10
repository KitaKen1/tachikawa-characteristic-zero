import OAI.RingTheory.Tachikawa.IntegerTensor

/-! Characteristic-independent excerpts from pinned OpenAI Math (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma map_id_underlying {M : ModuleCat A} {N N' : ModuleCat B} (g : N ⟶ N') :
    (map (k := k) (𝟙 M) g).restrictScalars k = (g.hom.restrictScalars k).lTensor M := rfl

lemma map_id_right_underlying {M M' : ModuleCat A} {N : ModuleCat B} (f : M ⟶ M') :
    (map (k := k) f (𝟙 N)).restrictScalars k = (f.hom.restrictScalars k).rTensor N := rfl

instance (N : ModuleCat B) : ((bifunctor k A B).flip.obj N).Additive where
  map_add {_X _Y} f f' := ModuleCat.hom_ext (map_add_left f f' (𝟙 N))

lemma exact_map_left (M : ModuleCat A) (S : ShortComplex (ModuleCat B)) (hS : S.Exact) :
    (S.map ((bifunctor k A B).obj M)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact M (show Function.Exact (S.f.hom.restrictScalars k)
    (S.g.hom.restrictScalars k) from hS)

lemma exact_map_right (N : ModuleCat B) (S : ShortComplex (ModuleCat A)) (hS : S.Exact) :
    (S.map ((bifunctor k A B).flip.obj N)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact N (show Function.Exact (S.f.hom.restrictScalars k)
    (S.g.hom.restrictScalars k) from hS)

instance (M : ModuleCat A) : PreservesFiniteLimits ((bifunctor k A B).obj M) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  refine ⟨exact_map_left M S hS.exact, ?_⟩
  rw [ModuleCat.mono_iff_injective]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := M)
    (S.f.hom.restrictScalars k) ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)

instance (M : ModuleCat A) : PreservesFiniteColimits ((bifunctor k A B).obj M) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  refine ⟨exact_map_left M S hS.exact, ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  exact LinearMap.lTensor_surjective M ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

instance (N : ModuleCat B) : PreservesFiniteLimits ((bifunctor k A B).flip.obj N) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  refine ⟨exact_map_right N S hS.exact, ?_⟩
  rw [ModuleCat.mono_iff_injective]
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := N)
    (S.f.hom.restrictScalars k) ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)

instance (N : ModuleCat B) : PreservesFiniteColimits ((bifunctor k A B).flip.obj N) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  refine ⟨exact_map_right N S hS.exact, ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  exact LinearMap.rTensor_surjective N ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

end Tachikawa.OuterTensor

namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

instance objFinite (M : ModuleCat.{0} A) (N : ModuleCat.{0} B)
    [FiniteDimensional k M] [FiniteDimensional k N] :
    Module.Finite (A ⊗[k] B) (Obj k A B M N) := by
  have : FiniteDimensional k (Obj k A B M N) := inferInstanceAs (FiniteDimensional k (M ⊗[k] N))
  exact Module.Finite.of_restrictScalars_finite k _ _

lemma isZero_obj_left (M : ModuleCat.{0} A) (N : ModuleCat.{0} B) (h : IsZero M) :
    IsZero (((bifunctor k A B).obj M).obj N) :=
  ((bifunctor k A B).flip.obj N).map_isZero h

lemma isZero_obj_right (M : ModuleCat.{0} A) (N : ModuleCat.{0} B) (h : IsZero N) :
    IsZero (((bifunctor k A B).obj M).obj N) := ((bifunctor k A B).obj M).map_isZero h

end Tachikawa.OuterTensor

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type} [Ring R] {ι : Type}

def coproductSupportIso (F : ι → ModuleCat R) (p : ι → Prop)
    (hz : ∀ i, ¬p i → IsZero (F i)) : (∐ F) ≅ ∐ (fun i : {i // p i} => F i.val) := by
  classical
  refine {
    hom := Sigma.desc fun i => if h : p i then Sigma.ι (fun i : {i // p i} => F i.val) ⟨i,h⟩ else 0
    inv := Sigma.desc fun i => Sigma.ι F i.val
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc]
    by_cases h : p i
    · simp only [dite_eq_left h, Sigma.ι_comp_desc, Category.comp_id]
    · simp only [dite_eq_right h, zero_comp, Category.comp_id]
      exact (hz i h).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, dite_eq_left i.property, Category.comp_id]

lemma coproduct_finite_of_support (F : ι → ModuleCat R) (p : ι → Prop)
    [Finite {i // p i}] (hz : ∀ i, ¬p i → IsZero (F i))
    (hf : ∀ i, Module.Finite R (F i)) : Module.Finite R (∐ F : ModuleCat R) := by
  let (i : {i // p i}) : Module.Finite R (F i.val) := hf i.val
  let J := fun i : {i // p i} => F i.val
  exact Module.Finite.equiv (((coproductSupportIso F p hz) ≪≫
    (biproduct.isoCoproduct J).symm ≪≫ ModuleCat.biproductIsoPi J).toLinearEquiv.symm)

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{0} A) ℤ) (Q : ChainComplex (ModuleCat.{0} B) ℤ)

lemma total_projective_int (hP : ∀ i, Module.Finite A (P.X i))
    (hQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i))
    (pQ : ∀ j, Module.Projective B (Q.X j)) (n : ℤ) :
    Projective ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let (i : ℤ) : Module.Finite A (P.X i) := hP i
  let (j : ℤ) : Module.Finite B (Q.X j) := hQ j
  let (i : ℤ) : Module.Projective A (P.X i) := pP i
  let (j : ℤ) : Module.Projective B (Q.X j) := pQ j
  have (i j : ℤ) : Module.Projective (A ⊗[k] B) (Obj k A B (P.X i) (Q.X j)) :=
    projective k A B _ _
  have (i j : ℤ) : Projective (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    change Projective (ModuleCat.of (A ⊗[k] B) (Obj k A B (P.X i) (Q.X j)))
    infer_instance
  change Projective (∐ fun ij : {ij : ℤ × ℤ // ij.1+ij.2=n} =>
    ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2))
  infer_instance

lemma total_isZero_below_int (a b : ℤ)
    (hP : ∀ i, i < a → IsZero (P.X i)) (hQ : ∀ j, j < b → IsZero (Q.X j))
    (n : ℤ) (hn : n < a+b) :
    IsZero ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have h : IsZero (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : i < a
    · exact isZero_obj_left _ _ (hP i hi)
    · exact isZero_obj_right _ _ (hQ j (by dsimp at hij; omega))
  exact h.eq_of_src _ _

lemma total_isZero_above_int (a b : ℤ)
    (hP : ∀ i, a < i → IsZero (P.X i)) (hQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℤ) (hn : a+b < n) :
    IsZero ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have h : IsZero (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : a < i
    · exact isZero_obj_left _ _ (hP i hi)
    · exact isZero_obj_right _ _ (hQ j (by dsimp at hij; omega))
  exact h.eq_of_src _ _

lemma total_finite_below_int (a b : ℤ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (zP : ∀ i, i < a → IsZero (P.X i)) (zQ : ∀ j, j < b → IsZero (Q.X j))
    (n : ℤ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=n}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let p : I → Prop := fun ij => a ≤ ij.val.1 ∧ b ≤ ij.val.2
  let : Finite {i // p i} := by
    let f : {i // p i} → Set.Icc a (n-b) := fun i => ⟨i.val.val.1, by
      have h := i.property
      have hi := i.val.property
      dsimp [p] at h
      exact ⟨h.1, by omega⟩⟩
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.val) h
    · have hh := congrArg (fun z => z.val) h
      have hx := x.val.property
      have hy := y.val.property
      change x.val.val.1 = y.val.val.1 at hh
      omega
  let (i : ℤ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℤ) : FiniteDimensional k (Q.X j) := hQ j
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  apply coproduct_finite_of_support F p
  · intro i hi
    by_cases h : a ≤ i.val.1
    · exact isZero_obj_right _ _ (zQ i.val.2 (by dsimp [p] at hi; omega))
    · exact isZero_obj_left _ _ (zP i.val.1 (by omega))
  · intro i
    exact objFinite _ _

lemma total_finite_above_int (a b : ℤ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (zP : ∀ i, a < i → IsZero (P.X i)) (zQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℤ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=n}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let p : I → Prop := fun ij => ij.val.1 ≤ a ∧ ij.val.2 ≤ b
  let : Finite {i // p i} := by
    let f : {i // p i} → Set.Icc (n-b) a := fun i => ⟨i.val.val.1, by
      have h := i.property
      have hi := i.val.property
      dsimp [p] at h
      exact ⟨by omega,h.1⟩⟩
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.val) h
    · have hh := congrArg (fun z => z.val) h
      have hx := x.val.property
      have hy := y.val.property
      change x.val.val.1 = y.val.val.1 at hh
      omega
  let (i : ℤ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℤ) : FiniteDimensional k (Q.X j) := hQ j
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  apply coproduct_finite_of_support F p
  · intro i hi
    by_cases h : i.val.1 ≤ a
    · exact isZero_obj_right _ _ (zQ i.val.2 (by dsimp [p] at hi; omega))
    · exact isZero_obj_left _ _ (zP i.val.1 (by omega))
  · intro i
    exact objFinite _ _

end Tachikawa.OuterTensor

end
end OAI
