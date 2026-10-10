import TachikawaCharZero.TwistedFactorization
import OAI.RingTheory.Tachikawa.NakayamaTransfer

/-! Package the ordinary rational obstruction as actual morphisms over
B⊗Bᵒᵖ. The intermediate outer object is End_Q(B), with left action by
precomposition and right action by postcomposition with right multiplication.
Its finite-additive closure is the ordinary obstruction class. Passage from
bounded derived perfect factors to this class remains a separate theorem. -/
namespace TachikawaCharZero.TwistedBimoduleObstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Finite sums and direct summands of one actual object. -/
def InAdd {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C] (W V : C) : Prop :=
  ∃ n : ℕ, Nonempty (Retract V (⨁ fun _ : Fin n => W))

section Generic
variable (k R : Type) [Field k] [Ring R] [Algebra k R]

def OuterEnd := R →ₗ[k] R
instance : FunLike (OuterEnd k R) R R := inferInstanceAs (FunLike (R →ₗ[k] R) R R)
instance : LinearMapClass (OuterEnd k R) k R R :=
  inferInstanceAs (LinearMapClass (R →ₗ[k] R) k R R)
instance : AddCommGroup (OuterEnd k R) := inferInstanceAs (AddCommGroup (R →ₗ[k] R))
instance : Module k (OuterEnd k R) := inferInstanceAs (Module k (R →ₗ[k] R))
@[ext] theorem outerEnd_ext {F G : OuterEnd k R} (h : ∀ x, F x=G x) : F=G :=
  LinearMap.ext h
instance : Module R (OuterEnd k R) where
  smul a F := (show R →ₗ[k] R from F).comp (LinearMap.mulRight k a)
  one_smul F := by ext x; change F (x*1)=F x; rw [mul_one]
  mul_smul a b F := by ext x; change F (x*(a*b))=F ((x*a)*b); rw [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a F G := by ext x; rfl
  add_smul a b F := by ext x; change F (x*(a+b))=F (x*a)+F (x*b); rw [mul_add,map_add]
  zero_smul F := by ext x; change F (x*0)=0; rw [mul_zero,map_zero]
instance : Module Rᵐᵒᵖ (OuterEnd k R) where
  smul a F := (LinearMap.mulRight k a.unop).comp (show R →ₗ[k] R from F)
  one_smul F := by ext x; change F x*1=F x; rw [mul_one]
  mul_smul a b F := by ext x; change F x*(b.unop*a.unop)=(F x*b.unop)*a.unop; rw [mul_assoc]
  smul_zero a := by ext x; change (0:R)*a.unop=0; rw [zero_mul]
  smul_add a F G := by ext x; change (F x+G x)*a.unop=F x*a.unop+G x*a.unop; rw [add_mul]
  add_smul a b F := by ext x; change F x*(a.unop+b.unop)=F x*a.unop+F x*b.unop; rw [mul_add]
  zero_smul F := by ext x; change F x*0=0; rw [mul_zero]
instance : SMulCommClass R Rᵐᵒᵖ (OuterEnd k R) where
  smul_comm a b F := by ext x; rfl
instance : IsScalarTower k R (OuterEnd k R) where
  smul_assoc c a F := by
    ext x
    change F (x*(c • a))=c • F (x*a)
    rw [Algebra.mul_smul_comm,map_smul]
instance : IsScalarTower k Rᵐᵒᵖ (OuterEnd k R) where
  smul_assoc c a F := by
    ext x
    change F x*(c • a.unop)=c • (F x*a.unop)
    exact Algebra.mul_smul_comm c (F x) a.unop

end Generic

section Underlying
variable {k R S M : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module R M] [Module Sᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]

def bimoduleUnderlying : Enveloping.ofBimodule (k := k) (R := R) (S := S) M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change Enveloping.action (k := k) (R := R) (S := S) M
      (algebraMap k (Enveloping.Alg k R S) c) x = c • (show M from x)
    rw [AlgHom.commutes]
    rfl

end Underlying

open TwistedFactorization
abbrev BE := Enveloping.Alg ℚ B₀ B₀
abbrev U := Enveloping.twistedRegular theta
def D : ModuleCat BE := Enveloping.ofBimodule (k := ℚ) (R := B₀) (S := B₀) (DualBimodule ℚ B₀)
def W : ModuleCat BE := Enveloping.ofBimodule (k := ℚ) (R := B₀) (S := B₀) (OuterEnd ℚ B₀)

def etaLinear : AlgebraInduction.Bimod theta.toAlgHom →ₗ[B₀] DualBimodule ℚ B₀ where
  toFun := eta
  map_add' := eta.map_add
  map_smul' a x := eta_left a x

def etaMap : U ⟶ D := Enveloping.ofBimoduleHom etaLinear
  (fun a x => by
    change eta ((show B₀ from x)*theta a.unop)=
      (eta (show B₀ from x)).comp (LinearMap.mulLeft ℚ a.unop)
    exact eta_twisted_right (show B₀ from x) a.unop)

def alphaUnderlying (a : U ⟶ W) : B₀ →ₗ[ℚ] (B₀ →ₗ[ℚ] B₀) where
  toFun x := show B₀ →ₗ[ℚ] B₀ from a (show U from x)
  map_add' x y := a.hom.map_add (show U from x) (show U from y)
  map_smul' c x := by
    -- Pin the tensor-product semiring before elaborating its algebra map.
    let scalar : BE := @algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c
    have h := a.hom.map_smul' scalar (show U from x)
    change a.hom ((Enveloping.action (k := ℚ) (R := B₀) (S := B₀)
      (AlgebraInduction.Bimod theta.toAlgHom) (@algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c)) x)=
        (Enveloping.action (k := ℚ) (R := B₀) (S := B₀) (OuterEnd ℚ B₀)
          (@algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c)) (show OuterEnd ℚ B₀ from a (show U from x)) at h
    erw [(Enveloping.action (k := ℚ) (R := B₀) (S := B₀)
      (AlgebraInduction.Bimod theta.toAlgHom)).commutes c,
        (Enveloping.action (k := ℚ) (R := B₀) (S := B₀) (OuterEnd ℚ B₀)).commutes c] at h
    exact h

def betaUnderlying (b : W ⟶ D) : (B₀ →ₗ[ℚ] B₀) →ₗ[ℚ] Module.Dual ℚ B₀ where
  toFun F := show Module.Dual ℚ B₀ from b (show W from F)
  map_add' F G := b.hom.map_add (show W from F) (show W from G)
  map_smul' c F := by
    let scalar : BE := @algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c
    have h := b.hom.map_smul' scalar (show W from F)
    change b.hom ((Enveloping.action (k := ℚ) (R := B₀) (S := B₀)
      (OuterEnd ℚ B₀) (@algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c)) F)=
        (Enveloping.action (k := ℚ) (R := B₀) (S := B₀) (DualBimodule ℚ B₀)
          (@algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c)) (show DualBimodule ℚ B₀ from b (show W from F)) at h
    erw [(Enveloping.action (k := ℚ) (R := B₀) (S := B₀) (OuterEnd ℚ B₀)).commutes c,
      (Enveloping.action (k := ℚ) (R := B₀) (S := B₀) (DualBimodule ℚ B₀)).commutes c] at h
    exact h

theorem mulRight_one : LinearMap.mulRight ℚ (1:B₀)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact mul_one x

theorem mulLeft_one : LinearMap.mulLeft ℚ (1:B₀)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact one_mul x

theorem alpha_left (a : U ⟶ W) (x y : B₀) :
    alphaUnderlying a (x*y)=(alphaUnderlying a y).comp (LinearMap.mulRight ℚ x) := by
  have h := a.hom.map_smul (x ⊗ₜ[ℚ] (1:B₀ᵐᵒᵖ)) (show U from y)
  change alphaUnderlying a (x*(y*theta 1))=
    ((LinearMap.mulRight ℚ 1).comp (alphaUnderlying a y)).comp (LinearMap.mulRight ℚ x) at h
  simpa only [map_one,mul_one,mulRight_one,LinearMap.id_comp] using h

theorem alpha_right (a : U ⟶ W) (x y : B₀) :
    alphaUnderlying a (x*theta y)=(LinearMap.mulRight ℚ y).comp (alphaUnderlying a x) := by
  have h := a.hom.map_smul ((1:B₀) ⊗ₜ[ℚ] MulOpposite.op y) (show U from x)
  change alphaUnderlying a (1*(x*theta y))=
    ((LinearMap.mulRight ℚ y).comp (alphaUnderlying a x)).comp (LinearMap.mulRight ℚ 1) at h
  simpa only [one_mul,mulRight_one,LinearMap.comp_id] using h

theorem beta_left (b : W ⟶ D) (x : B₀) (F : B₀ →ₗ[ℚ] B₀) :
    betaUnderlying b (F.comp (LinearMap.mulRight ℚ x))=
      (betaUnderlying b F).comp (LinearMap.mulRight ℚ x) := by
  have h := b.hom.map_smul (x ⊗ₜ[ℚ] (1:B₀ᵐᵒᵖ)) (show W from F)
  change betaUnderlying b (((LinearMap.mulRight ℚ 1).comp F).comp (LinearMap.mulRight ℚ x))=
    ((betaUnderlying b F).comp (LinearMap.mulLeft ℚ 1)).comp (LinearMap.mulRight ℚ x) at h
  simpa only [mulRight_one,mulLeft_one,LinearMap.id_comp,LinearMap.comp_id] using h

theorem beta_right (b : W ⟶ D) (x : B₀) (F : B₀ →ₗ[ℚ] B₀) :
    betaUnderlying b ((LinearMap.mulRight ℚ x).comp F)=
      (betaUnderlying b F).comp (LinearMap.mulLeft ℚ x) := by
  have h := b.hom.map_smul ((1:B₀) ⊗ₜ[ℚ] MulOpposite.op x) (show W from F)
  change betaUnderlying b (((LinearMap.mulRight ℚ x).comp F).comp (LinearMap.mulRight ℚ 1))=
    ((betaUnderlying b F).comp (LinearMap.mulLeft ℚ x)).comp (LinearMap.mulRight ℚ 1) at h
  simpa only [mulRight_one,LinearMap.comp_id] using h

theorem ordinary_vertex_zero (a : U ⟶ W) (b : W ⟶ D) :
    (show DualBimodule ℚ B₀ from (a ≫ b) (show U from (1:B₀))) (tensorVertex (2:ℚ))=0 :=
  ordinary_factorization_vertex_zero (alphaUnderlying a) (alpha_left a) (alpha_right a)
    (betaUnderlying b) (beta_left b) (beta_right b)

theorem etaMap_one_vertex :
    (show DualBimodule ℚ B₀ from etaMap (show U from (1:B₀))) (tensorVertex (2:ℚ))=1 :=
  eta_one_vertex

theorem etaMap_not_inAdd_factor {V : ModuleCat BE} (hV : InAdd W V)
    (a : U ⟶ V) (b : V ⟶ D) : a ≫ b ≠ etaMap := by
  classical
  obtain ⟨n,⟨r⟩⟩ := hV
  have he : ∑ i : Fin n, (a ≫ r.i ≫ biproduct.π (fun _ : Fin n => W) i) ≫
      (biproduct.ι (fun _ : Fin n => W) i ≫ r.r ≫ b) = a ≫ b := by
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum,← Preadditive.comp_sum]
    conv_lhs => arg 2; arg 2; simp only [← Category.assoc]
    rw [← Preadditive.sum_comp,← Preadditive.sum_comp,biproduct.total]
    simp only [Category.id_comp,← Category.assoc]
    rw [Category.assoc a,r.retract,Category.comp_id]
  intro hab
  have h := congrArg (fun f : U ⟶ D =>
    (show DualBimodule ℚ B₀ from f (show U from (1:B₀))) (tensorVertex (2:ℚ)))
    (he.trans hab)
  simp only [ModuleCat.hom_sum,LinearMap.sum_apply,etaMap_one_vertex] at h
  change (∑ i : Fin n, (show Module.Dual ℚ B₀ from
    ((a ≫ r.i ≫ biproduct.π (fun _ : Fin n => W) i) ≫
      (biproduct.ι (fun _ : Fin n => W) i ≫ r.r ≫ b)) (show U from (1:B₀))))
        (tensorVertex (2:ℚ))=1 at h
  rw [LinearMap.sum_apply] at h
  have hz : (∑ i : Fin n,
    (show DualBimodule ℚ B₀ from
      ((a ≫ r.i ≫ biproduct.π (fun _ : Fin n => W) i) ≫
        (biproduct.ι (fun _ : Fin n => W) i ≫ r.r ≫ b)) (show U from (1:B₀)))
          (tensorVertex (2:ℚ)))=0 :=
    Finset.sum_eq_zero (fun i _ => ordinary_vertex_zero _ _)
  exact zero_ne_one (hz.symm.trans h)

end
end TachikawaCharZero.TwistedBimoduleObstruction
