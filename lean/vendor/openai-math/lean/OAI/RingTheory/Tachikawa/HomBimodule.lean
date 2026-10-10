import OAI.RingTheory.Tachikawa.CompleteTensor
import OAI.RingTheory.Tachikawa.Twisting

/-! Characteristic-independent Hom bimodule and tensor-Hom adjunction
from OpenAI Math, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0). Excerpt declarations unchanged. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace HomBimodule
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) (Z : ModuleCat S)

def Base : Type := X →ₗ[k] Z
instance : CoeFun (Base (k := k) X Z) (fun _ => X → Z) := ⟨fun f => (show X →ₗ[k] Z from f)⟩
instance : AddCommGroup (Base (k := k) X Z) := inferInstanceAs (AddCommGroup (X →ₗ[k] Z))
instance : Module k (Base (k := k) X Z) := inferInstanceAs (Module k (X →ₗ[k] Z))
instance : Module S (Base (k := k) X Z) := inferInstanceAs (Module S (X →ₗ[k] Z))
instance : IsScalarTower k S (Base (k := k) X Z) :=
  inferInstanceAs (IsScalarTower k S (X →ₗ[k] Z))

def rightAction : Rᵐᵒᵖ →+* Module.End S (Base (k := k) X Z) where
  toFun r :=
    { toFun := fun f => (show X →ₗ[k] Z from f).comp ((Algebra.lsmul k k X) r.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact congrArg f (one_smul R x)
  map_mul' r s := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact congrArg f (mul_smul s.unop r.unop x)
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    change f ((0:R) • x) = 0
    exact (congrArg f (zero_smul R x)).trans (show X →ₗ[k] Z from f).map_zero
  map_add' r s := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact (congrArg f (add_smul r.unop s.unop x)).trans (f.map_add _ _)

instance : Module Rᵐᵒᵖ (Base (k := k) X Z) := Module.compHom _ (rightAction (k := k) X Z)
instance : SMulCommClass S Rᵐᵒᵖ (Base (k := k) X Z) where
  smul_comm _ _ _ := rfl
instance : IsScalarTower k Rᵐᵒᵖ (Base (k := k) X Z) :=
  IsScalarTower.of_algebraMap_smul fun c f => by
    apply LinearMap.ext
    intro x
    change f ((algebraMap k R c) • x) = c • f x
    rw [IsScalarTower.algebraMap_smul]
    exact f.map_smul c x

def obj : ModuleCat (Enveloping.Alg k S R) :=
  Enveloping.ofBimodule (k := k) (R := S) (S := R) (Base (k := k) X Z)

lemma tmul_smul_apply (s : S) (r : Rᵐᵒᵖ) (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z from ((s ⊗ₜ[k] r) • f)) x =
      s • (show X →ₗ[k] Z from f) (r.unop • x) := rfl

lemma left_smul_apply (s : S) (f : Enveloping.Obj (obj (k := k) X Z)) (x : X) :
    (show X →ₗ[k] Z from (s • f)) x = s • (show X →ₗ[k] Z from f) x := by
  change s • (show X →ₗ[k] Z from f) ((1:R) • x) = _
  rw [one_smul]

lemma right_smul_apply (r : Rᵐᵒᵖ) (f : Enveloping.Obj (obj (k := k) X Z)) (x : X) :
    (show X →ₗ[k] Z from (r • f)) x = (show X →ₗ[k] Z from f) (r.unop • x) := by
  change (1:S) • (show X →ₗ[k] Z from f) (r.unop • x) = _
  rw [one_smul]

lemma k_smul_apply (c : k) (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z from (c • f)) x = c • (show X →ₗ[k] Z from f) x := by
  change (show X →ₗ[k] Z from ((algebraMap k (Enveloping.Alg k S R) c) • f)) x = _
  change (show X →ₗ[k] Z from (((algebraMap k S c) ⊗ₜ[k] (1:Rᵐᵒᵖ)) • f)) x = _
  apply Eq.trans (tmul_smul_apply X Z (algebraMap k S c) 1 f x)
  exact (congrArg (fun y : X => (algebraMap k S c) • (show X →ₗ[k] Z from f) y)
    (one_smul R x)).trans (IsScalarTower.algebraMap_smul S c ((show X →ₗ[k] Z from f) x))

end HomBimodule



namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat (Enveloping.Alg k S R)} {X : ModuleCat R} {Z : ModuleCat S}

def uncurryLinear (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    Enveloping.Obj M →ₗ[S] (X →ₗ[k] Z) where
  toFun := fun m => f m
  map_add' a b := f.hom.map_add a b
  map_smul' s m := by
    apply LinearMap.ext
    intro x
    exact (congrArg (fun h : Enveloping.Obj (HomBimodule.obj (k := k) X Z) =>
      (show X →ₗ[k] Z from h) x) ((Enveloping.leftMap f).map_smul s m)).trans
        (HomBimodule.left_smul_apply X Z s (f m) x)

lemma uncurryLinear_balanced (f : M ⟶ HomBimodule.obj (k := k) X Z)
    (r : R) (m : Enveloping.Obj M) (x : X) :
    uncurryLinear f (MulOpposite.op r • m) x = uncurryLinear f m (r • x) :=
  (congrArg (fun h : Enveloping.Obj (HomBimodule.obj (k := k) X Z) =>
      (show X →ₗ[k] Z from h) x) ((Enveloping.rightMap f).map_smul (MulOpposite.op r) m)).trans
    (HomBimodule.right_smul_apply X Z (MulOpposite.op r) (f m) x)

def uncurry (f : M ⟶ HomBimodule.obj (k := k) X Z) : Enveloping.evalObj X M ⟶ Z :=
  ModuleCat.ofHom (BalancedTensor.lift (uncurryLinear f) (uncurryLinear_balanced f))

@[simp] lemma uncurry_mk (f : M ⟶ HomBimodule.obj (k := k) X Z)
    (m : Enveloping.Obj M) (x : X) :
    uncurry f (BalancedTensor.mk m x) = (show X →ₗ[k] Z from f m) x := rfl

def curryLinear (g : Enveloping.evalObj X M ⟶ Z) :
    Enveloping.Obj M →ₗ[S] HomBimodule.Base (k := k) X Z where
  toFun m := (g.hom.restrictScalars k).comp (BalancedTensor.mk m)
  map_add' m n := by
    apply LinearMap.ext
    intro x
    change g (BalancedTensor.mk (m+n) x) = g (BalancedTensor.mk m x) + g (BalancedTensor.mk n x)
    exact (congrArg g (congrArg (fun h : X →ₗ[k] Enveloping.evalType X M => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Enveloping.Obj M) (N := X)).map_add m n))).trans
      (g.hom.map_add _ _)
  map_smul' s m := by
    apply LinearMap.ext
    intro x
    change g (BalancedTensor.mk (s • m) x) = s • g (BalancedTensor.mk m x)
    exact (congrArg g (congrArg (fun h : X →ₗ[k] Enveloping.evalType X M => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Enveloping.Obj M) (N := X)).map_smul s m))).trans
      (g.hom.map_smul s _)

lemma curryLinear_right (g : Enveloping.evalObj X M ⟶ Z) (r : Rᵐᵒᵖ) (m : Enveloping.Obj M) :
    curryLinear g (r • m) = r • curryLinear g m := by
  apply LinearMap.ext
  intro x
  change g (BalancedTensor.mk (r • m) x) = g (BalancedTensor.mk m (r.unop • x))
  exact congrArg g (BalancedTensor.balance r.unop m x)

def curry (g : Enveloping.evalObj X M ⟶ Z) : M ⟶ HomBimodule.obj (k := k) X Z :=
  (Enveloping.reassembleIso M).inv ≫
    Enveloping.ofBimoduleHom (curryLinear g) (curryLinear_right g)

@[simp] lemma curry_apply (g : Enveloping.evalObj X M ⟶ Z) (m : M) (x : X) :
    (show X →ₗ[k] Z from curry g m) x = g (BalancedTensor.mk (show Enveloping.Obj M from m) x) := rfl

lemma uncurry_curry (g : Enveloping.evalObj X M ⟶ Z) : uncurry (curry g) = g := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

lemma curry_uncurry (f : M ⟶ HomBimodule.obj (k := k) X Z) : curry (uncurry f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  rfl

def equiv : (M ⟶ HomBimodule.obj (k := k) X Z) ≃ₗ[k] (Enveloping.evalObj X M ⟶ Z) where
  toFun := uncurry
  invFun := curry
  left_inv := curry_uncurry
  right_inv := uncurry_curry
  map_add' f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    exact HomBimodule.k_smul_apply X Z c (f m) x

lemma uncurry_precompose {N : ModuleCat (Enveloping.Alg k S R)}
    (a : N ⟶ M) (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    uncurry (a ≫ f) = Enveloping.evalMap X a ≫ uncurry f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

end BimoduleTensorHom
end Tachikawa


namespace Tachikawa.HomBimodule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (X : ModuleCat R)

def representationLinear : R →ₗ[R] Base (k := k) X X where
  toFun a := (Algebra.lsmul k k X) a
  map_add' a b := map_add (Algebra.lsmul k k X) a b
  map_smul' a b := by
    apply LinearMap.ext
    intro x
    exact mul_smul a b x

def representation : Enveloping.regular (k := k) (R := R) ⟶ obj (k := k) X X :=
  Enveloping.ofBimoduleHom (representationLinear (k := k) X) (by
    intro a b
    apply LinearMap.ext
    intro x
    exact mul_smul b a.unop x)

@[simp] lemma representation_apply (a : Enveloping.regular (k := k) (R := R)) (x : X) :
    (show X →ₗ[k] X from representation X a) x = (show R from a) • x := rfl

end Tachikawa.HomBimodule


end
end OAI
