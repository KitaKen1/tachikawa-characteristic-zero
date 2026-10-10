import OAI.RingTheory.Tachikawa.HomBimodule

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.HomBimodule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) {Z Z' : ModuleCat S}

def postLinear (g : Z ⟶ Z') : Base (k := k) X Z →ₗ[S] Base (k := k) X Z' where
  toFun f := (g.hom.restrictScalars k).comp (show X →ₗ[k] Z from f)
  map_add' f h := by
    apply LinearMap.ext
    intro x
    exact g.hom.map_add _ _
  map_smul' s f := by
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul s _

def postMap (g : Z ⟶ Z') : obj (k := k) X Z ⟶ obj (k := k) X Z' :=
  Enveloping.ofBimoduleHom (postLinear X g) (fun _ _ => rfl)

@[simp] lemma postMap_apply (g : Z ⟶ Z') (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z' from postMap X g f) x = g ((show X →ₗ[k] Z from f) x) := rfl

lemma postMap_surjective (g : Z ⟶ Z') (hg : Function.Surjective g) :
    Function.Surjective (postMap (k := k) X g) := by
  intro f
  obtain ⟨p, hp⟩ := Module.projective_lifting_property (g.hom.restrictScalars k)
    (show X →ₗ[k] Z' from f) hg
  refine ⟨p, ?_⟩
  exact hp

instance (g : Z ⟶ Z') [Epi g] : Epi (postMap (k := k) X g) :=
  (ModuleCat.epi_iff_surjective _).mpr (postMap_surjective X g ((ModuleCat.epi_iff_surjective g).mp inferInstance))

end Tachikawa.HomBimodule



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat.{0} (Enveloping.Alg k S R)} {X : ModuleCat.{0} R} {Z Z' : ModuleCat.{0} S}

lemma uncurry_postcompose (f : M ⟶ HomBimodule.obj (k := k) X Z) (g : Z ⟶ Z') :
    uncurry (f ≫ HomBimodule.postMap X g) = uncurry f ≫ g := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

end BimoduleTensorHom
namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) (M : ModuleCat.{0} (Alg k S R))

instance evaluation_projective [CategoryTheory.Projective M] :
    CategoryTheory.Projective (evalObj X M) where
  factors {Z Z'} f g _ := by
    obtain ⟨h, hh⟩ := CategoryTheory.Projective.factors (BimoduleTensorHom.curry f)
      (HomBimodule.postMap (k := k) X g)
    refine ⟨BimoduleTensorHom.uncurry h, ?_⟩
    rw [← BimoduleTensorHom.uncurry_postcompose, hh, BimoduleTensorHom.uncurry_curry]

end Enveloping
end Tachikawa

end
end OAI
