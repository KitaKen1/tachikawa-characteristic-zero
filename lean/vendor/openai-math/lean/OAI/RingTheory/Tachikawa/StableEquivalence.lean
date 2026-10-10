import OAI.RingTheory.Tachikawa.TwistHom

/-! Characteristic-independent excerpts from OpenAI Math Perfect.lean,
fixed commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Source line ranges are recorded in vendor/openai-math/manifest.json.
Excerpt declarations are unchanged; imports and outer wrappers differ. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev StableMap (M N : ModuleCat.{0} R) :=
  StableHom (k := k) (R := R) (M := M) (N := N)

structure StableEquiv (M N : ModuleCat.{0} R) where
  hom : M →ₗ[R] N
  inv : N →ₗ[R] M
  inv_hom : inv.comp hom - LinearMap.id ∈ projectiveFactors (k := k)
  hom_inv : hom.comp inv - LinearMap.id ∈ projectiveFactors (k := k)

variable {M N L : ModuleCat.{0} R}

lemma stableClass_eq_iff (f g : M →ₗ[R] N) :
    stableClass (k := k) f = stableClass (k := k) g ↔
      f-g ∈ projectiveFactors (k := k) := by
  rw [← sub_eq_zero, ← map_sub, stableClass_eq_zero_iff]

def stablePrecompose (g : L →ₗ[R] M) : StableMap (k := k) M N →ₗ[k] StableMap (k := k) L N :=
  (projectiveFactors (k := k)).mapQ (projectiveFactors (k := k))
    (homPrecompose g) (fun _ hf => projectiveFactors_precomp hf g)

@[simp] lemma stablePrecompose_class (g : L →ₗ[R] M) (f : M →ₗ[R] N) :
    stablePrecompose (k := k) g (stableClass (k := k) f) =
      stableClass (k := k) (f.comp g) := rfl

namespace StableEquiv

def refl (M : ModuleCat.{0} R) : StableEquiv (k := k) M M where
  hom := LinearMap.id
  inv := LinearMap.id
  inv_hom := by simp only [LinearMap.id_comp, sub_self]; exact Submodule.zero_mem _
  hom_inv := by simp only [LinearMap.id_comp, sub_self]; exact Submodule.zero_mem _

def symm (e : StableEquiv (k := k) M N) : StableEquiv (k := k) N M where
  hom := e.inv
  inv := e.hom
  inv_hom := e.hom_inv
  hom_inv := e.inv_hom

def ofLinearEquiv (e : M ≃ₗ[R] N) : StableEquiv (k := k) M N where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  inv_hom := by
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; exact e.symm_apply_apply x
    rw [h, sub_self]; exact Submodule.zero_mem _
  hom_inv := by
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; exact e.apply_symm_apply x
    rw [h, sub_self]; exact Submodule.zero_mem _

lemma post_inverse (e : StableEquiv (k := k) M N) (f : L →ₗ[R] M) :
    stableClass (k := k) (e.inv.comp (e.hom.comp f)) = stableClass (k := k) f := by
  apply (stableClass_eq_iff _ _).mpr
  have h := projectiveFactors_precomp e.inv_hom f
  simpa only [LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc] using h

lemma pre_inverse (e : StableEquiv (k := k) M N) (f : M →ₗ[R] L) :
    stableClass (k := k) ((f.comp e.inv).comp e.hom) = stableClass (k := k) f := by
  apply (stableClass_eq_iff _ _).mpr
  have h := projectiveFactors_postcomp e.inv_hom f
  simpa only [LinearMap.comp_sub, LinearMap.comp_id, LinearMap.comp_assoc] using h

def post (e : StableEquiv (k := k) M N) (L : ModuleCat.{0} R) :
    StableMap (k := k) L M ≃ₗ[k] StableMap (k := k) L N :=
  { stablePostcompose e.hom with
    invFun := stablePostcompose e.inv
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.post_inverse f
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.symm.post_inverse f }

def pre (e : StableEquiv (k := k) M N) (L : ModuleCat.{0} R) :
    StableMap (k := k) M L ≃ₗ[k] StableMap (k := k) N L :=
  { stablePrecompose e.inv with
    invFun := stablePrecompose e.hom
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.pre_inverse f
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.symm.pre_inverse f }

def trans (e : StableEquiv (k := k) M N) (d : StableEquiv (k := k) N L) :
    StableEquiv (k := k) M L where
  hom := d.hom.comp e.hom
  inv := e.inv.comp d.inv
  inv_hom := by
    have h := projectiveFactors_postcomp (projectiveFactors_precomp d.inv_hom e.hom) e.inv
    have heq : (e.inv.comp d.inv).comp (d.hom.comp e.hom) - LinearMap.id =
        (e.inv.comp ((d.inv.comp d.hom - LinearMap.id).comp e.hom)) +
        (e.inv.comp e.hom - LinearMap.id) := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_assoc]
      abel
    rw [heq]
    exact Submodule.add_mem _ h e.inv_hom
  hom_inv := by
    have h := projectiveFactors_postcomp (projectiveFactors_precomp e.hom_inv d.inv) d.hom
    have heq : (d.hom.comp e.hom).comp (e.inv.comp d.inv) - LinearMap.id =
        (d.hom.comp ((e.hom.comp e.inv - LinearMap.id).comp d.inv)) +
        (d.hom.comp d.inv - LinearMap.id) := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_assoc]
      abel
    rw [heq]
    exact Submodule.add_mem _ h d.hom_inv

end StableEquiv
end Tachikawa

end
end OAI
