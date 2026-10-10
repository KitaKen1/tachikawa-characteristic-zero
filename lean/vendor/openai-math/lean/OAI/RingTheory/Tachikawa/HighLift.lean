import OAI.RingTheory.Tachikawa.PerfectCutoff
import OAI.RingTheory.Tachikawa.InducedRegular

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R S : Type} [Ring R] [Ring S]

lemma resolution_reflect_exact {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] (n : ℕ) (hn : 0 < n)
    (h : Function.Exact (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d (n+1) n)
      (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d n (n-1))) :
    Function.Exact ((reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)).d
      ((n:ℤ)+1) n)
      ((reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)).d n ((n:ℤ)-1)) := by
  let K := (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex
  let L := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let A : ShortComplex (ModuleCat.{0} S) :=
    ShortComplex.mk (K.d (-((n:ℤ)+1)) (-(n:ℤ))) (K.d (-(n:ℤ)) (-((n:ℤ)-1))) (by simp)
  let B : ShortComplex (ModuleCat.{0} S) :=
    ShortComplex.mk (L.d (n+1) n) (L.d n (n-1)) (by simp)
  let e₁ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)+1)) (n+1) (by omega))
  let e₂ := F.mapIso (P.cochainComplexXIso (-(n:ℤ)) n)
  let e₃ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)-1)) (n-1) (by omega))
  have h₁ : e₁.hom ≫ B.f = A.f ≫ e₂.hom := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [P.cochainComplex_d (-((n:ℤ)+1)) (-(n:ℤ)) (n+1) n (by omega) rfl]
    simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₂ : e₂.hom ≫ B.g = A.g ≫ e₃.hom := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [P.cochainComplex_d (-(n:ℤ)) (-((n:ℤ)-1)) n (n-1) rfl (by omega)]
    simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : B.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact B).mpr h
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact A).mp
    (ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂).symm he)

end Tachikawa

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma projectiveResolution_reflect_exact {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (n : ℕ) (hn : 0 < n) :
    Function.Exact ((reflectCochain P.cochainComplex).d ((n:ℤ)+1) n)
      ((reflectCochain P.cochainComplex).d n ((n:ℤ)-1)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ m)
  exact resolution_reflect_exact P (𝟭 (ModuleCat.{0} R)) (m+1) (by omega)
    (by
      change Function.Exact (P.complex.d (m+1+1) (m+1)) (P.complex.d (m+1) (m+1-1))
      rw [show m+1-1=m by omega]
      exact h)

theorem stably_nonzero_high_lift [Module.Injective R R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ)
    (pproj : ∀ j, Module.Projective R (P.X j)) (M : FiniteModule k R)
    (v : P ⟶ (CochainComplex.singleFunctor _ 0).obj M.obj)
    (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hex : ∀ n : ℕ, n₀ ≤ n → Function.Exact ((reflectCochain P).d ((n:ℤ)+1) n)
      ((reflectCochain P).d n ((n:ℤ)-1)))
    (hnot : ∀ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      ( _hfin : ∀ j, Module.Finite R (L.X j)) ( _hproj : ∀ j, Module.Projective R (L.X j))
      (l u : ℤ) ( _hb : ∀ j, j < l ∨ u < j → IsZero (L.X j))
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)),
      a ≫ b ≠ DerivedCategory.Q.map v)
    (f : P ⟶ M.projectiveResolution.cochainComplex)
    (hfv : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' =
      DerivedCategory.Q.map v) :
    ∀ n : ℕ, n₀ ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let Q := M.projectiveResolution
  intro n hn hz
  have hq (j : ℤ) (hj : (n:ℤ) ≤ j) :
      Function.Exact ((reflectCochain Q.cochainComplex).d (j+1) j)
        ((reflectCochain Q.cochainComplex).d j (j-1)) := by
    lift j to ℕ using (show 0 ≤ j by omega) with m hm
    subst hm
    exact projectiveResolution_reflect_exact Q m (by omega)
  have qproj (j : ℤ) : Module.Projective R (Q.cochainComplex.X j) := by infer_instance
  have qfin (j : ℤ) : Module.Finite R (Q.cochainComplex.X j) :=
    finite_resolution_cochain Q (fun _ => inferInstance) j
  have qb (j : ℤ) (hj : -(0:ℤ) < j) : Subsingleton (Q.cochainComplex.X j) :=
    ModuleCat.isZero_iff_subsingleton.mp (Q.cochainComplex.isZero_of_isStrictlyLE 0 j (by omega))
  obtain ⟨L,a,b,he,hlp,hlf,hlb⟩ := cochain_perfect_factorization f n 0 (hex n hn)
    hq pproj qproj qfin qb hz
  apply hnot L hlf hlp (-(n:ℤ)+1) 0 (by simpa only [neg_zero] using hlb) a
    (b ≫ DerivedCategory.Q.map Q.π')
  rw [← Category.assoc,he,hfv]

theorem exists_stably_nonzero_high_lift [Module.Injective R R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ) [P.IsKProjective]
    (pproj : ∀ j, Module.Projective R (P.X j)) (M : FiniteModule k R)
    (v : P ⟶ (CochainComplex.singleFunctor _ 0).obj M.obj)
    (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hex : ∀ n : ℕ, n₀ ≤ n → Function.Exact ((reflectCochain P).d ((n:ℤ)+1) n)
      ((reflectCochain P).d n ((n:ℤ)-1)))
    (hnot : ∀ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      ( _hfin : ∀ j, Module.Finite R (L.X j)) ( _hproj : ∀ j, Module.Projective R (L.X j))
      (l u : ℤ) ( _hb : ∀ j, j < l ∨ u < j → IsZero (L.X j))
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)),
      a ≫ b ≠ DerivedCategory.Q.map v) :
    ∃ f : P ⟶ M.projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' =
        DerivedCategory.Q.map v ∧
      ∀ n : ℕ, n₀ ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let Q := M.projectiveResolution
  obtain ⟨f,hf⟩ := kProjective_chain_representative P Q.cochainComplex
    (DerivedCategory.Q.map v ≫ inv (DerivedCategory.Q.map Q.π'))
  have hfv : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map Q.π' = DerivedCategory.Q.map v := by
    rw [hf]; simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]
  exact ⟨f,hfv,stably_nonzero_high_lift P pproj M v n₀ hn₀ hex hnot f hfv⟩

end Tachikawa

end
end OAI
