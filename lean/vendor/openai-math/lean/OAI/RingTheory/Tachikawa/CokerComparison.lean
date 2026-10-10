import OAI.RingTheory.Tachikawa.HighLift

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R S : Type} [Ring R] [Ring S]

def cokerLinearEquiv {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B] [Module R C] [Module R D]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D) (e : A ≃ₗ[R] C) (v : B ≃ₗ[R] D)
    (h : v.toLinearMap.comp f = g.comp e.toLinearMap) :
    (B ⧸ LinearMap.range f) ≃ₗ[R] (D ⧸ LinearMap.range g) :=
  Submodule.Quotient.equiv _ _ v (by
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨e z,(LinearMap.congr_fun h z).symm⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨z,rfl⟩ := e.surjective y
      exact ⟨f z,⟨z,rfl⟩,LinearMap.congr_fun h z⟩)

def resolutionReflectCokerEquiv {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] (n : ℕ) :
    CokerAt (reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)) n ≃ₗ[S]
      (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).X n ⧸
        LinearMap.range (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d (n+1) n).hom) := by
  let e₁ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)+1)) (n+1) (by omega))
  let e₂ := F.mapIso (P.cochainComplexXIso (-(n:ℤ)) n)
  apply cokerLinearEquiv _ _ e₁.toLinearEquiv e₂.toLinearEquiv
  apply ModuleCat.hom_ext_iff.mp
  change F.map (P.cochainComplex.d _ _) ≫ F.map _ = F.map _ ≫ F.map (P.complex.d _ _)
  rw [P.cochainComplex_d (-((n:ℤ)+1)) (-(n:ℤ)) (n+1) n (by omega) rfl]
  simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

namespace FiniteModule
variable {k : Type} [Field k] [Algebra k R] [FiniteDimensional k R] (M : FiniteModule k R)
lemma pos_cover_exact (n : ℕ) :
    Function.Exact (M.posDifferential n) (M.positive n).cover.map := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (M.positive (n+1)).cover.surjective ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · rintro ⟨y,rfl⟩
    exact ((M.positive (n+1)).cover.map y).property

def naturalCokerPositiveEquiv (n : ℕ) :
    (M.projectiveResolution.complex.X n ⧸ LinearMap.range (M.projectiveResolution.complex.d (n+1) n).hom)
      ≃ₗ[R] (M.positive n).obj := by
  have hd : (M.projectiveResolution.complex.d (n+1) n).hom = M.posDifferential n := by
    dsimp only [projectiveResolution, resolutionOfExact]
    exact congrArg ModuleCat.Hom.hom (ChainComplex.of_d _ _ n)
  change (M.posTerm n ⧸ LinearMap.range (M.projectiveResolution.complex.d (n+1) n).hom) ≃ₗ[R] _
  exact (Submodule.quotEquivOfEq _ _ (hd ▸ (M.pos_cover_exact n).linearMap_ker_eq.symm)).trans
    ((M.positive n).cover.map.quotKerEquivOfSurjective (M.positive n).cover.surjective)

def reflectCokerPositiveEquiv (n : ℕ) :
    CokerAt (reflectCochain M.projectiveResolution.cochainComplex) n ≃ₗ[R] (M.positive n).obj :=
  (resolutionReflectCokerEquiv M.projectiveResolution (𝟭 (ModuleCat R)) n).trans
    (M.naturalCokerPositiveEquiv n)
end FiniteModule
end Tachikawa

end
end OAI
