import OAI.RingTheory.Tachikawa.InductionAdjunction

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

abbrev leftIndObj (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) : ModuleCat (Alg k S U) :=
  ofBimodule (k := k) (R := S) (S := U)
    (BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M))

def leftIndMap (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k R U)} (f : M ⟶ N) :
    leftIndObj φ M ⟶ leftIndObj φ N :=
  ofBimoduleHom (BalancedTensor.mapRight (k := k) (S := S) (M := AlgebraInduction.Bimod φ) (leftMap f))
    (by
      intro u x
      induction x using BalancedTensor.induction_on with
      | h0 => simp only [smul_zero, map_zero]
      | ht s m =>
        change BalancedTensor.mk (k := k) (R := R) (S := S) s (show Obj N from f (u • m)) =
          BalancedTensor.mk s (u • (show Obj N from f m))
        exact congrArg (BalancedTensor.mk s) ((rightMap f).map_smul u m)
      | ha x y hx hy => simp only [smul_add, map_add, hx, hy])

def leftIndFunctor (φ : R →ₐ[k] S) : ModuleCat (Alg k R U) ⥤ ModuleCat (Alg k S U) where
  obj := leftIndObj φ
  map := leftIndMap φ
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | h0 => rfl
    | ht s m => rfl
    | ha x y hx hy =>
      exact ((leftIndMap φ (𝟙 M)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((ModuleCat.Hom.hom (𝟙 (leftIndObj φ M))).map_add x y).symm)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | h0 => rfl
    | ht s m => rfl
    | ha x y hx hy =>
      exact ((leftIndMap φ (f ≫ g)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((leftIndMap φ f ≫ leftIndMap φ g).hom.map_add x y).symm)

instance (φ : R →ₐ[k] S) : (leftIndFunctor (U := U) φ).Additive where
  map_add {_X _Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (leftIndMap φ (f + g)).hom x = ((leftIndMap φ f) + (leftIndMap φ g)).hom x
    induction x using BalancedTensor.induction_on (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj _X) with
    | h0 => rfl
    | ht s m =>
      exact (BalancedTensor.mk (k := k) (R := R) (S := S)
        (M := AlgebraInduction.Bimod φ) (N := Obj _Y) s).map_add (f m) (g m)
    | ha x y hx hy =>
      exact ((leftIndMap φ (f+g)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((leftIndMap φ f + leftIndMap φ g).hom.map_add x y).symm)

def leftIndUnderlyingIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (leftFunctor (k := k) (R := S) (S := U)).obj (leftIndObj φ M) ≅
      (AlgebraInduction.functor φ).obj ((leftFunctor (k := k) (R := R) (S := U)).obj M) :=
  LinearEquiv.toModuleIso
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' s x := by
      change (action (k := k) (R := S) (S := U)
        (BalancedTensor.T (k := k) (R := R) (S := S)
          (M := AlgebraInduction.Bimod φ) (N := Obj M)) (s ⊗ₜ[k] (1:Uᵐᵒᵖ))) x = _
      change s • ((1:Uᵐᵒᵖ) • (show BalancedTensor.T (k := k) (R := R) (S := S)
        (M := AlgebraInduction.Bimod φ) (N := Obj M) from x)) = _
      rw [one_smul]
      rfl }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k U R : Type} [Field k] [Ring U] [Ring R] [Algebra k U] [Algebra k R]

def RightObj (M : ModuleCat (Alg k U R)) := (rightFunctor (k := k) (R := U) (S := R)).obj M
instance (M : ModuleCat (Alg k U R)) : AddCommGroup (RightObj M) :=
  inferInstanceAs (AddCommGroup ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : Module Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (Module Rᵐᵒᵖ ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : Module k (RightObj M) :=
  inferInstanceAs (Module k ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : IsScalarTower k Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (IsScalarTower k Rᵐᵒᵖ ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : Module U (RightObj M) :=
  inferInstanceAs (Module U (Obj M))
instance (M : ModuleCat (Alg k U R)) : SMulCommClass U Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (SMulCommClass U Rᵐᵒᵖ (Obj M))
instance (M : ModuleCat (Alg k U R)) : IsScalarTower k U (RightObj M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (algebraMap k U c) • (show Obj M from x) =
      (algebraMap k Rᵐᵒᵖ c) • (show Obj M from x)
    rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]

def rightObjMap {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) : RightObj M →ₗ[Rᵐᵒᵖ] RightObj N :=
  rightMap f

def rightObjLeftMap {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) : RightObj M →ₗ[U] RightObj N :=
  leftMap f

end Tachikawa.Enveloping



namespace Tachikawa.BalancedTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U M N : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [Module U N]
  [IsScalarTower k R N] [IsScalarTower k U N] [SMulCommClass U R N]

def commutingAction : U →+* Module.End S (T (k := k) (R := R) (S := S) (M := M) (N := N)) where
  toFun u := mapRight ((Algebra.lsmul k R N) u)
  map_one' := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) 1) = LinearMap.id
    rw [map_one]
    exact mapRight_id
  map_mul' u v := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) (u*v)) = _
    rw [map_mul]
    exact mapRight_comp _ _
  map_zero' := by rw [map_zero]; exact mapRight_zero
  map_add' u v := by rw [map_add]; exact mapRight_add _ _

end Tachikawa.BalancedTensor



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def RightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :=
  BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)

instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : AddCommGroup (RightIndType φ M) :=
  inferInstanceAs (AddCommGroup (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module k (RightIndType φ M) :=
  inferInstanceAs (Module k (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module Sᵐᵒᵖ (RightIndType φ M) :=
  inferInstanceAs (Module Sᵐᵒᵖ (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : IsScalarTower k Sᵐᵒᵖ (RightIndType φ M) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module U (RightIndType φ M) :=
  show Module U (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)) from
  Module.compHom _ (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : IsScalarTower k U (RightIndType φ M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
    | h0 => exact (smul_zero (algebraMap k U c) : (algebraMap k U c) • (0 : RightIndType φ M) = 0).trans (smul_zero c).symm
    | ht s m =>
      change BalancedTensor.mk s ((algebraMap k U c) • m) = c • BalancedTensor.mk s m
      rw [IsScalarTower.algebraMap_smul]
      exact (BalancedTensor.mk s).map_smul c m
    | ha x y hx hy =>
      change ((algebraMap k U c) • (show RightIndType φ M from x+y)) = c • (show RightIndType φ M from x+y)
      exact (smul_add (algebraMap k U c) (show RightIndType φ M from x) (show RightIndType φ M from y)).trans
        ((congrArg₂ (fun x y : RightIndType φ M => x+y) hx hy).trans
          (smul_add c (show RightIndType φ M from x) (show RightIndType φ M from y)).symm)
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : SMulCommClass U Sᵐᵒᵖ (RightIndType φ M) where
  smul_comm u s x := by
    change (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u) (s • x) =
      s • (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u) x
    exact (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u).map_smul s x

abbrev rightIndObj (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : ModuleCat (Alg k U S) :=
  ofBimodule (k := k) (R := U) (S := S) (RightIndType φ M)

abbrev rightEnvelopingMap (φ : R →ₐ[k] S) : Alg k U R →ₐ[k] Alg k U S :=
  Algebra.TensorProduct.map (AlgHom.id k U) φ.op




lemma rightInd_smul_mk (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (u : U)
    (s : AlgebraInduction.Bimod φ.op) (m : RightObj M) :
    u • (show RightIndType φ M from BalancedTensor.mk s m) =
      (show RightIndType φ M from BalancedTensor.mk s (u • m)) := rfl

lemma rightInd_smul_tmul (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R))
    (u : U) (s : Sᵐᵒᵖ) (x : RightIndType φ M) :
    (u ⊗ₜ[k] s) • (show rightIndObj φ M from x) = (show RightIndType φ M from u • s • x) := rfl

def rightIndUnit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj (rightIndObj φ M) :=
  ModuleCat.ofHom (X := M)
    (Y := (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj (rightIndObj φ M))
  { toFun := fun m => BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ)) (show RightObj M from m)
    map_add' := by intro m n; exact (BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj M) (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ))).map_add m n
    map_smul' a m := by
      let t : RightObj M →ₗ[k] RightIndType φ M := BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
        (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ))
      change t (show RightObj M from a • m) =
        (action (k := k) (R := U) (S := S) (RightIndType φ M) (rightEnvelopingMap φ a)) (t m)
      induction a using TensorProduct.inductionOn with
      | tmul u r =>
        change t (show RightObj M from (u ⊗ₜ[k] r) • m) = u • (φ.op r • t m)
        rw [smul_comm u (φ.op r)]
        change t (show RightObj M from (u ⊗ₜ[k] r) • m) = φ.op r • t (u • (show RightObj M from m))
        trans t (r • u • (show RightObj M from m))
        · apply congrArg t
          exact (tmul_smul M u r m).trans (smul_comm u r (show RightObj M from m))
        exact (AlgebraInduction.unit φ.op (ModuleCat.of Rᵐᵒᵖ (RightObj M))).hom.map_smul r (u • (show RightObj M from m))
      | add a b ha hb =>
        rw [map_add, map_add]
        exact (congrArg (fun x : M => t (show RightObj M from x)) (add_smul a b m)).trans
          ((t.map_add _ _).trans (congrArg₂ (fun x y => x+y) ha hb)) }




def rightIndMapLinear (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) :
    RightIndType φ M →ₗ[U] RightIndType φ N where
  toFun := BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ) (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)
  map_add' := (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).map_add
  map_smul' u x := by
    induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
    | h0 => rfl
    | ht s m =>
      change BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ) s (show RightObj N from f (u • m)) =
        BalancedTensor.mk s (u • (show RightObj N from f m))
      exact congrArg (BalancedTensor.mk s) ((rightObjLeftMap f).map_smul u m)
    | ha x y hx hy =>
      let g : RightIndType φ M →ₗ[k] RightIndType φ N :=
        (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
          (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).restrictScalars k
      change g (u • (show RightIndType φ M from x+y)) = u • g (x+y)
      exact (congrArg g (smul_add u (show RightIndType φ M from x) (show RightIndType φ M from y))).trans
        ((g.map_add _ _).trans ((congrArg₂ (fun x y : RightIndType φ N => x+y) hx hy).trans
          ((smul_add u (g x) (g y)).symm.trans
            (congrArg (fun z : RightIndType φ N => u • z) (g.map_add x y).symm))))

def rightIndMap (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) :
    rightIndObj φ M ⟶ rightIndObj φ N :=
  ofBimoduleHom (rightIndMapLinear φ f) (by
    intro s x
    exact (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).map_smul s x)

lemma rightInd_hom_ext (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    {f g : rightIndObj φ M ⟶ N}
    (h : ∀ (s : AlgebraInduction.Bimod φ.op) (m : RightObj M),
      f (BalancedTensor.mk s m) = g (BalancedTensor.mk s m)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
  | h0 => exact f.hom.map_zero.trans g.hom.map_zero.symm
  | ht s m => exact h s m
  | ha x y hx hy =>
    exact (f.hom.map_add x y).trans
      ((congrArg₂ (fun x y => x+y) hx hy).trans (g.hom.map_add x y).symm)

def rightIndFunctor (φ : R →ₐ[k] S) : ModuleCat (Alg k U R) ⥤ ModuleCat (Alg k U S) where
  obj := rightIndObj φ
  map := rightIndMap φ
  map_id M := by apply rightInd_hom_ext φ; intro s m; rfl
  map_comp f g := by apply rightInd_hom_ext φ; intro s m; rfl

instance (φ : R →ₐ[k] S) : (rightIndFunctor (U := U) φ).Additive where
  map_add {_X _Y f g} := by
    apply rightInd_hom_ext φ
    intro s m
    exact (BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj _Y) s).map_add (f m) (g m)

def rightIndUnderlyingIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (rightFunctor (k := k) (R := U) (S := S)).obj (rightIndObj φ M) ≅
      (AlgebraInduction.functor φ.op).obj ((rightFunctor (k := k) (R := U) (S := R)).obj M) :=
  LinearEquiv.toModuleIso
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' s x := by
      change (1:U) • (s • (show RightIndType φ M from x)) = s • (show RightIndType φ M from x)
      rw [one_smul] }

def rightIndUnderlyingComparison (φ : R →ₐ[k] S) :
    rightIndFunctor (U := U) φ ⋙ rightFunctor ≅ rightFunctor ⋙ AlgebraInduction.functor φ.op :=
  NatIso.ofComponents (rightIndUnderlyingIso φ) (by intro M N f; ext x; rfl)




def rightIndResMap (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    ModuleCat.of Rᵐᵒᵖ (RightObj M) ⟶ (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ (RightObj N)) :=
  ModuleCat.ofHom (X := ModuleCat.of Rᵐᵒᵖ (RightObj M))
    (Y := (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ (RightObj N)))
  { toFun := fun m => (show RightObj N from f m)
    map_add' := f.hom.map_add
    map_smul' r m := by
      have h := f.hom.map_smul ((1:U) ⊗ₜ[k] r) m
      change (show N from f (((1:U) ⊗ₜ[k] r) • (show M from m))) =
        (rightEnvelopingMap φ ((1:U) ⊗ₜ[k] r)) • (show N from f m) at h
      exact h }

lemma rightIndResMap_left (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) (u : U) (m : RightObj M) :
    (show RightObj N from f (u • m)) = u • (show RightObj N from f m) := by
  have h := f.hom.map_smul (u ⊗ₜ[k] (1:Rᵐᵒᵖ)) m
  change (show N from f ((u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show M from m))) =
    rightEnvelopingMap φ (u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show N from f m) at h
  change (show N from f ((u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show M from m))) =
    (u ⊗ₜ[k] (1:Sᵐᵒᵖ)) • (show N from f m)
  simpa only [rightEnvelopingMap, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using h

def rightIndExtendRightLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    RightIndType φ M →ₗ[Sᵐᵒᵖ] RightObj N :=
  (AlgebraInduction.extend φ.op (rightIndResMap φ f)).hom

lemma rightIndExtendRightLinear_left (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) (u : U) (x) :
    rightIndExtendRightLinear φ f (u • x) = u • rightIndExtendRightLinear φ f x := by
  induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
  | h0 =>
    exact (congrArg (rightIndExtendRightLinear φ f) (smul_zero u)).trans
      ((rightIndExtendRightLinear φ f).map_zero.trans (smul_zero u).symm)
  | ht s m =>
    change (show Sᵐᵒᵖ from s) • (show RightObj N from f (u • m)) =
      u • ((show Sᵐᵒᵖ from s) • (show RightObj N from f m))
    rw [rightIndResMap_left φ f]
    exact (smul_comm u (show Sᵐᵒᵖ from s) (show RightObj N from f m)).symm
  | ha x y hx hy =>
    change rightIndExtendRightLinear φ f (u • (show RightIndType φ M from x+y)) = _
    exact (congrArg (rightIndExtendRightLinear φ f)
      (smul_add u (show RightIndType φ M from x) (show RightIndType φ M from y))).trans
      (((rightIndExtendRightLinear φ f).map_add _ _).trans
        ((congrArg₂ (fun x y : RightObj N => x+y) hx hy).trans
          ((smul_add u _ _).symm.trans (congrArg (fun x : RightObj N => u • x)
            ((rightIndExtendRightLinear φ f).map_add x y).symm))))

def rightIndExtendLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    RightIndType φ M →ₗ[U] RightObj N where
  toFun := rightIndExtendRightLinear φ f
  map_add' := (rightIndExtendRightLinear φ f).map_add
  map_smul' := rightIndExtendRightLinear_left φ f

def rightReassembleIso (M : ModuleCat (Alg k U S)) :
    ofBimodule (k := k) (R := U) (S := S) (RightObj M) ≅ M :=
  LinearEquiv.toModuleIso (show (ofBimodule (k := k) (R := U) (S := S) (RightObj M)) ≃ₗ[Alg k U S] M from
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a x := by
      change (show M from (action (k := k) (R := U) (S := S) (RightObj M) a) x) = a • (show M from x)
      induction a using TensorProduct.inductionOn with
      | tmul r s => exact (tmul_smul M r s x).symm
      | add a b ha hb =>
        rw [map_add, add_smul]
        exact congrArg₂ (fun x y : M => x+y) ha hb })

def rightIndExtend (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    rightIndObj φ M ⟶ N :=
  ofBimoduleHom (rightIndExtendLinear φ f)
    (fun s x => (rightIndExtendRightLinear φ f).map_smul s x) ≫ (rightReassembleIso N).hom




def rightIndComparisonHom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M ⟶ rightIndObj φ M :=
  AlgebraInduction.extend (k := k) (R := Alg k U R) (S := Alg k U S)
    (N := M) (P := rightIndObj φ M) (rightEnvelopingMap φ) (rightIndUnit φ M)

def rightIndComparisonInv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndObj φ M ⟶ (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M :=
  rightIndExtend (k := k) (R := R) (S := S) (U := U) φ (M := M)
    (N := (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M)
    (AlgebraInduction.unit (k := k) (R := Alg k U R) (S := Alg k U S)
      (rightEnvelopingMap (U := U) φ) M)

lemma rightIndComparison_inv_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (m : M) :
    rightIndComparisonInv φ M (rightIndUnit φ M m) =
      AlgebraInduction.unit (k := k) (R := Alg k U R) (S := Alg k U S) (rightEnvelopingMap φ) M m := by
  change (1:Sᵐᵒᵖ) • (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
    AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m) = _
  exact one_smul _ _

lemma rightIndComparison_hom_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (m : M) :
    rightIndComparisonHom φ M (AlgebraInduction.unit (k := k) (R := Alg k U R)
      (S := Alg k U S) (rightEnvelopingMap φ) M m) = rightIndUnit φ M m := by
  change (1:Alg k U S) • (show rightIndObj φ M from rightIndUnit φ M m) = _
  exact one_smul _ _

lemma rightIndComparison_hom_inv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndComparisonHom φ M ≫ rightIndComparisonInv φ M = 𝟙 _ := by
  apply (AlgebraInduction.homEquiv (k := k) (R := Alg k U R) (S := Alg k U S)
    (rightEnvelopingMap φ) M _).injective
  ext m
  change rightIndComparisonInv φ M (rightIndComparisonHom φ M
    (AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)) =
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m
  rw [rightIndComparison_hom_unit, rightIndComparison_inv_unit]

lemma rightIndComparison_inv_hom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndComparisonInv φ M ≫ rightIndComparisonHom φ M = 𝟙 _ := by
  apply rightInd_hom_ext φ
  intro s m
  have h := (rightObjMap (rightIndComparisonHom φ M)).map_smul (show Sᵐᵒᵖ from s)
    (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)
  change rightIndComparisonHom φ M ((show Sᵐᵒᵖ from s) •
    (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)) = _
  apply h.trans
  apply Eq.trans (congrArg (fun x : RightObj (rightIndObj φ M) => (show Sᵐᵒᵖ from s) • x)
    (rightIndComparison_hom_unit φ M m))
  change (1:U) • ((show Sᵐᵒᵖ from s) •
    (show RightIndType φ M from BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)
      (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ)) m)) = BalancedTensor.mk s m
  rw [one_smul]
  exact (AlgebraInduction.mk_one_smul φ.op (ModuleCat.of Rᵐᵒᵖ (RightObj M)) (show Sᵐᵒᵖ from s) m).symm

def rightIndComparisonIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M ≅ rightIndObj φ M where
  hom := rightIndComparisonHom φ M
  inv := rightIndComparisonInv φ M
  hom_inv_id := rightIndComparison_hom_inv φ M
  inv_hom_id := rightIndComparison_inv_hom φ M

def rightIndComparison (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (rightEnvelopingMap (U := U) φ) ≅ rightIndFunctor φ :=
  NatIso.ofComponents (rightIndComparisonIso φ) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro a m
    change (show Alg k U S from a) • (show rightIndObj φ N from rightIndUnit φ N (f m)) =
      rightIndMap φ f ((show Alg k U S from a) • (show rightIndObj φ M from rightIndUnit φ M m))
    exact ((rightIndMap φ f).hom.map_smul (show Alg k U S from a)
      (show rightIndObj φ M from rightIndUnit φ M m)).symm)

end Tachikawa.Enveloping


end
end OAI
