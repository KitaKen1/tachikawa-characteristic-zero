import OAI.RingTheory.Tachikawa.CompleteResolution

/-! Characteristic-independent excerpts from pinned OpenAI Math,
commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (N : ModuleCat R)

lemma stableCoker_subsingleton (j : ℤ) (hz : ∀ f : P.X j ⟶ N, f = 0) :
    Subsingleton (StableHom (k := k) (R := R) (M := CokerAt P j) (N := N)) := by
  have hzero (x : StableHom (k := k) (R := R) (M := CokerAt P j) (N := N)) : x = 0 := by
    obtain ⟨f,rfl⟩ := stableClass_surjective x
    have hf : f = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
      exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
        (hz (ModuleCat.ofHom (f.comp (CokerAt.π P j))))) y
    rw [hf,map_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

def cokerHomIsolated (j : ℤ) (hz : ∀ f : P.X (j+1) ⟶ N, f = 0) :
    (P.X j ⟶ N) →ₗ[k] (CokerAt P j →ₗ[R] N) where
  toFun f := CokerAt.descend P j f.hom
    (ModuleCat.hom_ext_iff.mp (hz (P.d (j+1) j ≫ f)))
  map_add' f g := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl

def stableCokerIsolatedEquiv (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    (j : ℤ) (hnext : ∀ f : P.X (j+1) ⟶ N, f = 0)
    (hprev : ∀ f : P.X (j-1) ⟶ N, f = 0) :
    (P.X j ⟶ N) ≃ₗ[k] StableHom (k := k) (R := R) (M := CokerAt P j) (N := N) := by
  let d := cokerHomIsolated (k := k) P N j hnext
  let e := (stableClass (k := k)).comp d
  refine LinearEquiv.ofBijective e ⟨?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hf' : d f ∈ projectiveFactors (k := k) := (stableClass_eq_zero_iff _).mp hf
    obtain ⟨g,hg⟩ := (hP.factors_iff_boundary (k := k) fin proj j f.hom
      (ModuleCat.hom_ext_iff.mp (hnext (P.d (j+1) j ≫ f)))).mp hf'
    have hg0 : g = 0 := ModuleCat.hom_ext_iff.mp (hprev (ModuleCat.ofHom g))
    apply ModuleCat.hom_ext
    rw [hg0, LinearMap.zero_comp] at hg
    exact hg.symm
  · intro x
    obtain ⟨f,rfl⟩ := stableClass_surjective x
    refine ⟨ModuleCat.ofHom (f.comp (CokerAt.π P j)), ?_⟩
    apply congrArg (stableClass (k := k))
    apply LinearMap.ext
    intro y
    obtain ⟨z,rfl⟩ := CokerAt.π_surjective P j y
    rfl

end Tachikawa

end
end OAI
