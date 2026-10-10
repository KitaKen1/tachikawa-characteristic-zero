import OAI.RingTheory.Tachikawa.OuterTensor

/-! Characteristic-independent excerpts from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; source files, exact line ranges and hashes are
recorded in vendor/openai-math/manifest.json. -/
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


end
end OAI
