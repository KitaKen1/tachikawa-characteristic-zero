import OAI.RingTheory.Tachikawa.SideProjectivity
import OAI.RingTheory.Tachikawa.StableEvaluation

/-! Characteristic-independent excerpts from OpenAI Math Delta.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def leftProdEquiv (M N : ModuleCat (Alg k R S)) :
    Obj (ModuleCat.of (Alg k R S) (M × N)) ≃ₗ[R] (Obj M × Obj N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightProdEquiv (M N : ModuleCat (Alg k R S)) :
    Obj (ModuleCat.of (Alg k R S) (M × N)) ≃ₗ[Sᵐᵒᵖ] (Obj M × Obj N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (U V Y : FiniteModule k (Alg k R S)) (g : U.obj ⟶ Y.obj) (h : V.obj ⟶ Y.obj)

def fiberCover : ModuleCat (Alg k R S) := ModuleCat.of (Alg k R S) (Fin Y.cover.rank → Alg k R S)
def fiberMiddle : ModuleCat (Alg k R S) :=
  ModuleCat.of (Alg k R S) (U.obj × (V.obj × fiberCover Y))

def fiberProjection : fiberMiddle U V Y ⟶ Y.obj :=
  ModuleCat.ofHom (g.hom.coprod (h.hom.coprod Y.cover.map))

omit [FiniteDimensional k R] [FiniteDimensional k S] in
lemma fiberProjection_surjective : Function.Surjective (fiberProjection U V Y g h) := by
  intro y
  obtain ⟨z,hz⟩ := Y.cover.surjective y
  refine ⟨(0,(0,z)),?_⟩
  change g 0 + (h 0 + Y.cover.map z) = y
  rw [map_zero,map_zero,zero_add,zero_add,hz]

def fiber : FiniteModule k (Alg k R S) where
  obj := ModuleCat.of (Alg k R S) (LinearMap.ker (fiberProjection U V Y g h).hom)
  finite := by
    let : IsNoetherianRing (Alg k R S) := IsNoetherianRing.of_finite k (Alg k R S)
    let : Module.Finite (Alg k R S) (fiberMiddle U V Y) := by
      change Module.Finite (Alg k R S) (U.obj × (V.obj × (Fin Y.cover.rank → Alg k R S)))
      infer_instance
    exact Module.Finite.of_injective (LinearMap.ker (fiberProjection U V Y g h).hom).subtype
      Subtype.val_injective

def fiberInclusion : (fiber U V Y g h).obj ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom (LinearMap.ker (fiberProjection U V Y g h).hom).subtype

lemma fiberInclusion_injective : Function.Injective (fiberInclusion U V Y g h) :=
  Subtype.val_injective

lemma fiber_exact : Function.Exact (fiberInclusion U V Y g h) (fiberProjection U V Y g h) := by
  intro x
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩

lemma fiber_left_projective [Module.Projective R (Obj U.obj)]
    [Module.Projective R (Obj V.obj)] [Module.Projective R (Obj Y.obj)] :
    Module.Projective R (Obj (fiber U V Y g h).obj) := by
  let : Module.Projective R (Obj (fiberCover Y)) := freeLeftProjective _
  let : Module.Projective R (Obj (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))) :=
    Module.Projective.of_equiv (leftProdEquiv V.obj (fiberCover Y)).symm
  let : Module.Projective R (Obj (fiberMiddle U V Y)) :=
    Module.Projective.of_equiv (leftProdEquiv U.obj
      (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))).symm
  exact projective_kernel_of_surjective (leftMap (fiberInclusion U V Y g h))
    (leftMap (fiberProjection U V Y g h)) (fiberInclusion_injective U V Y g h)
    (fiberProjection_surjective U V Y g h) (fiber_exact U V Y g h)

lemma fiber_right_projective [Module.Projective Sᵐᵒᵖ (Obj U.obj)]
    [Module.Projective Sᵐᵒᵖ (Obj V.obj)] [Module.Projective Sᵐᵒᵖ (Obj Y.obj)] :
    Module.Projective Sᵐᵒᵖ (Obj (fiber U V Y g h).obj) := by
  let : Module.Projective Sᵐᵒᵖ (Obj (fiberCover Y)) := freeRightProjective _
  let : Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))) :=
    Module.Projective.of_equiv (rightProdEquiv V.obj (fiberCover Y)).symm
  let : Module.Projective Sᵐᵒᵖ (Obj (fiberMiddle U V Y)) :=
    Module.Projective.of_equiv (rightProdEquiv U.obj
      (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))).symm
  exact projective_kernel_of_surjective (rightMap (fiberInclusion U V Y g h))
    (rightMap (fiberProjection U V Y g h)) (fiberInclusion_injective U V Y g h)
    (fiberProjection_surjective U V Y g h) (fiber_exact U V Y g h)

end Enveloping
end Tachikawa


namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (U V Y : FiniteModule k (Alg k R S))

def fiberInl : U.obj ⟶ fiberMiddle U V Y := ModuleCat.ofHom (LinearMap.inl _ _ _)
def fiberInm : V.obj ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom ((LinearMap.inr _ _ _).comp (LinearMap.inl _ _ _))
def fiberInr : fiberCover Y ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom ((LinearMap.inr _ _ _).comp (LinearMap.inr _ _ _))
def fiberFst : fiberMiddle U V Y ⟶ U.obj := ModuleCat.ofHom (LinearMap.fst _ _ _)
def fiberSnd : fiberMiddle U V Y ⟶ V.obj :=
  ModuleCat.ofHom ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))

@[simp] lemma fiberInl_fst : fiberInl U V Y ≫ fiberFst U V Y = 𝟙 _ := rfl
@[simp] lemma fiberInl_snd : fiberInl U V Y ≫ fiberSnd U V Y = 0 := rfl
@[simp] lemma fiberInm_fst : fiberInm U V Y ≫ fiberFst U V Y = 0 := rfl
@[simp] lemma fiberInm_snd : fiberInm U V Y ≫ fiberSnd U V Y = 𝟙 _ := rfl
@[simp] lemma fiberInr_fst : fiberInr U V Y ≫ fiberFst U V Y = 0 := rfl
@[simp] lemma fiberInr_snd : fiberInr U V Y ≫ fiberSnd U V Y = 0 := rfl

variable (g : U.obj ⟶ Y.obj) (h : V.obj ⟶ Y.obj)
@[simp] lemma fiberInl_projection : fiberInl U V Y ≫ fiberProjection U V Y g h = g := by
  ext x
  change g x + (h 0 + Y.cover.map 0) = g x
  simp only [map_zero,add_zero]
@[simp] lemma fiberInm_projection : fiberInm U V Y ≫ fiberProjection U V Y g h = h := by
  ext x
  change g 0 + (h x + Y.cover.map 0) = h x
  simp only [map_zero,add_zero,zero_add]
@[simp] lemma fiberInr_projection : fiberInr U V Y ≫ fiberProjection U V Y g h =
    ModuleCat.ofHom Y.cover.map := by
  ext x
  change g 0 + (h 0 + Y.cover.map x) = Y.cover.map x
  simp only [map_zero,zero_add]
end Tachikawa.Enveloping


namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {X M F Y Q : ModuleCat R}

lemma exists_stable_kernel_lift (i : F ⟶ M) (p : M ⟶ Y) (j : Q ⟶ M)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hq : Function.Surjective (j ≫ p)) (a : X ⟶ M)
    (ha : stableClass (k := k) (a ≫ p).hom = 0) :
    ∃ (v : X ⟶ F) (b : X ⟶ Q), v ≫ i = a - b ≫ j := by
  obtain ⟨P,hfin,hproj,u,w,hw⟩ := (stableClass_eq_zero_iff _).mp ha
  let := hproj
  obtain ⟨l,hl⟩ := Module.projective_lifting_property (j ≫ p).hom w hq
  let b : X ⟶ Q := ModuleCat.ofHom (l.comp u)
  have hzero : (a - b ≫ j) ≫ p = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change p (a x - j (l (u x))) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hw x
    change w (u x) = p (a x) at h
    have h' := LinearMap.congr_fun hl (u x)
    change p (j (l (u x))) = w (u x) at h'
    rw [h',h,sub_self]
  let e := LinearEquiv.ofInjective i.hom hi
  have hr (x : X) : (a - b ≫ j) x ∈ LinearMap.range i.hom := by
    exact (he _).mp (congrArg (fun f => f x) hzero)
  let c : X →ₗ[R] LinearMap.range i.hom := (a - b ≫ j).hom.codRestrict _ hr
  refine ⟨ModuleCat.ofHom (e.symm.toLinearMap.comp c), b, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (e.apply_symm_apply (c x))

end Tachikawa


namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (U V Y : FiniteModule k (Alg k R S))

def fiberThird : fiberMiddle U V Y ⟶ fiberCover Y :=
  ModuleCat.ofHom ((LinearMap.snd (Alg k R S) V.obj (fiberCover Y)).comp
    (LinearMap.snd (Alg k R S) U.obj (V.obj × fiberCover Y)))

lemma fiber_sum_id : fiberFst U V Y ≫ fiberInl U V Y +
    fiberSnd U V Y ≫ fiberInm U V Y + fiberThird U V Y ≫ fiberInr U V Y = 𝟙 _ := by
  ext x
  change (x.1,(0,0)) + (0,(x.2.1,0)) + (0,(0,x.2.2)) = x
  rcases x with ⟨x,y,z⟩
  apply Prod.ext
  · change (x+0)+0=x
    simp
  · apply Prod.ext
    · change (0+y)+0=y
      simp
    · change (0+0)+z=z
      simp
end Tachikawa.Enveloping

end
end OAI
