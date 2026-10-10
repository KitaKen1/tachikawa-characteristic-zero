import OAI.RingTheory.Tachikawa.InducedSideResolution
import OAI.RingTheory.Tachikawa.RestrictedRegular

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace NatCoker
variable (P : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
abbrev C := P.X (n+1) ⧸ LinearMap.range (P.d (n+2) (n+1)).hom

def π : P.X (n+1) →ₗ[R] C P n := (LinearMap.range (P.d (n+2) (n+1)).hom).mkQ

def ι : C P n →ₗ[R] P.X n :=
  (LinearMap.range (P.d (n+2) (n+1)).hom).liftQ (P.d (n+1) n).hom (by
    rintro x ⟨y,rfl⟩
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (P.d_comp_d (n+2) (n+1) n)) y)

lemma projective_of_contraction [Module.Projective R (P.X n)]
    (a : P.X n →ₗ[R] P.X (n+1)) (b : P.X (n+1) →ₗ[R] P.X (n+2))
    (h : a.comp (P.d (n+1) n).hom + (P.d (n+2) (n+1)).hom.comp b = LinearMap.id) :
    Module.Projective R (C P n) := by
  apply Module.Projective.of_split (ι P n) ((π P n).comp a)
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n+2) (n+1)).hom) x
  change π P n (a (P.d (n+1) n y)) = π P n y
  have he := congrArg (π P n) (LinearMap.congr_fun h y)
  change π P n (a (P.d (n+1) n y) + P.d (n+2) (n+1) (b y)) = π P n y at he
  rw [map_add] at he
  have hz : π P n (P.d (n+2) (n+1) (b y)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨b y,rfl⟩
  simpa only [hz,add_zero] using he

lemma projective_of_homotopy {Q : ChainComplex (ModuleCat R) ℕ}
    (e : HomotopyEquiv P Q) [Subsingleton (Q.X (n+1))]
    [Module.Projective R (P.X n)] : Module.Projective R (C P n) := by
  let h := e.homotopyHomInvId.symm
  have he := h.comm (n+1)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at he
  have hz : (e.hom ≫ e.inv).f (n+1) = 0 := by
    apply ModuleCat.hom_ext
    ext x
    change e.inv.f (n+1) (e.hom.f (n+1) x) = 0
    rw [Subsingleton.elim (e.hom.f (n+1) x) 0, map_zero]
  rw [hz,add_zero] at he
  exact projective_of_contraction P n (h.hom n (n+1)).hom (h.hom (n+1) (n+2)).hom
    (ModuleCat.hom_ext_iff.mp he.symm)

end NatCoker
end Tachikawa

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (φ : R →ₐ[k] S)


def inducedRegularComplex : ChainComplex (ModuleCat.{0} (Alg k S S)) ℕ :=
  ((AlgebraInduction.functor (envelopingMap φ)).mapHomologicalComplex (.down ℕ)).obj
    (regularResolution (k := k) (R := R)).complex

instance inducedRegularComplex_finite (n : ℕ) :
    FiniteDimensional k ((inducedRegularComplex φ).X n) := by
  change FiniteDimensional k
    ((AlgebraInduction.functor (envelopingMap φ)).obj ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  infer_instance

instance inducedRegularComplex_finiteAlg (n : ℕ) :
    Module.Finite (Alg k S S) ((inducedRegularComplex φ).X n) :=
  Module.Finite.of_restrictScalars_finite k _ _

instance inducedRegularComplex_projective (n : ℕ) :
    Module.Projective (Alg k S S) ((inducedRegularComplex φ).X n) := by
  change Module.Projective (Alg k S S)
    ((AlgebraInduction.functor (envelopingMap φ)).obj ((regularResolution (k := k) (R := R)).complex.X n))
  infer_instance

instance inducedRegularComplex_leftProjective (n : ℕ) :
    Module.Projective S (Obj ((inducedRegularComplex φ).X n)) := projective_left _

instance inducedRegularComplex_rightProjective (n : ℕ) :
    Module.Projective Sᵐᵒᵖ (Obj ((inducedRegularComplex φ).X n)) := projective_right _


end Tachikawa.Enveloping

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def LeftRestrictedRegular (_φ : R →ₐ[k] S) := S
instance (φ : R →ₐ[k] S) : AddCommGroup (LeftRestrictedRegular φ) := inferInstanceAs (AddCommGroup S)
instance (φ : R →ₐ[k] S) : Module k (LeftRestrictedRegular φ) := inferInstanceAs (Module k S)
instance (φ : R →ₐ[k] S) : Module R (LeftRestrictedRegular φ) := Module.compHom S φ.toRingHom
instance (φ : R →ₐ[k] S) : Module Sᵐᵒᵖ (LeftRestrictedRegular φ) := inferInstanceAs (Module Sᵐᵒᵖ S)
instance (φ : R →ₐ[k] S) : IsScalarTower k R (LeftRestrictedRegular φ) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change φ (algebraMap k R c) * (show S from x) = c • (show S from x)
    rw [φ.commutes, Algebra.smul_def]
instance (φ : R →ₐ[k] S) : IsScalarTower k Sᵐᵒᵖ (LeftRestrictedRegular φ) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ S)
instance (φ : R →ₐ[k] S) : SMulCommClass R Sᵐᵒᵖ (LeftRestrictedRegular φ) where
  smul_comm r s x := (mul_assoc (φ r) (show S from x) s.unop).symm

abbrev leftRestrictedRegular (φ : R →ₐ[k] S) : ModuleCat (Alg k R S) :=
  ofBimodule (k := k) (R := R) (S := S) (LeftRestrictedRegular φ)

def regularRightUnitTarget (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (rightEnvelopingMap (U := R) φ)).obj (leftRestrictedRegular φ) :=
  ModuleCat.ofHom (X := regular (k := k) (R := R))
    (Y := (AlgebraInduction.res (rightEnvelopingMap (U := R) φ)).obj (leftRestrictedRegular φ))
  { toFun := fun r => φ r
    map_add' := φ.map_add
    map_smul' a x := by
      change φ ((action (k := k) (R := R) (S := R) R a) x) =
        (action (k := k) (R := R) (S := S) (LeftRestrictedRegular φ) (rightEnvelopingMap φ a)) (φ x)
      induction a using TensorProduct.inductionOn with
      | tmul r s =>
        change φ (r * ((show R from x) * s.unop)) = φ r * (φ x * φ s.unop)
        rw [map_mul, map_mul]
      | add a b ha hb =>
        rw [map_add, map_add, map_add]
        change φ ((action (k := k) (R := R) (S := R) R a) x +
          (action (k := k) (R := R) (S := R) R b) x) = _
        exact (φ.map_add _ _).trans (congrArg₂ (fun x y : LeftRestrictedRegular φ => x+y) ha hb) }

def rightIndRegularHom (φ : R →ₐ[k] S) :
    rightIndObj φ (regular (k := k) (R := R)) ⟶ leftRestrictedRegular φ :=
  rightIndExtend φ (regularRightUnitTarget φ)

lemma rightIndRegularHom_mk (φ : R →ₐ[k] S) (s : AlgebraInduction.Bimod φ.op)
    (r : RightObj (regular (k := k) (R := R))) :
    (show S from rightIndRegularHom φ (BalancedTensor.mk s r)) = φ r * (show Sᵐᵒᵖ from s).unop := by
  change φ (1:R) * (φ r * (show Sᵐᵒᵖ from s).unop) = _
  rw [map_one, one_mul]

def rightIndRegularInvLinear (φ : R →ₐ[k] S) : S →ₗ[Sᵐᵒᵖ]
    RightIndType φ (regular (k := k) (R := R)) :=
  ((LinearMap.toSpanSingleton Sᵐᵒᵖ _)
    (show RightIndType φ (regular (k := k) (R := R)) from
      rightIndUnit φ (regular (k := k) (R := R)) (1:R))).comp
    (MulOpposite.opLinearEquiv Sᵐᵒᵖ).toLinearMap

lemma rightIndRegularInvLinear_apply (φ : R →ₐ[k] S) (s : S) :
    rightIndRegularInvLinear φ s = BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj (regular (k := k) (R := R)))
      (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (1:R) := by
  exact (AlgebraInduction.mk_one_smul φ.op
    (ModuleCat.of Rᵐᵒᵖ (RightObj (regular (k := k) (R := R)))) (MulOpposite.op s) (1:R)).symm

lemma rightIndRegularInvLinear_left (φ : R →ₐ[k] S) (r : R) (s : S) :
    rightIndRegularInvLinear φ (φ r * s) = r • rightIndRegularInvLinear φ s := by
  rw [rightIndRegularInvLinear_apply, rightIndRegularInvLinear_apply]
  trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj (regular (k := k) (R := R)))
    (MulOpposite.op (MulOpposite.op r) • (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)) (1:R)
  · rfl
  trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)
    (MulOpposite.op r • (show RightObj (regular (k := k) (R := R)) from (1:R)))
  · exact BalancedTensor.balance _ _ _
  change BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (1 * (1 * r)) =
    BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (r * (1 * 1))
  exact congrArg (fun z : R => BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)
    (show RightObj (regular (k := k) (R := R)) from z)) (show (1:R) * (1*r) = r * (1*1) by simp only [one_mul, mul_one])

def rightIndRegularInv (φ : R →ₐ[k] S) :
    leftRestrictedRegular φ ⟶ rightIndObj φ (regular (k := k) (R := R)) :=
  ofBimoduleHom
    (show LeftRestrictedRegular φ →ₗ[R] RightIndType φ (regular (k := k) (R := R)) from
      { toFun := rightIndRegularInvLinear φ
        map_add' := (rightIndRegularInvLinear φ).map_add
        map_smul' := rightIndRegularInvLinear_left φ })
    (fun s x => (rightIndRegularInvLinear φ).map_smul s x)

def rightIndRegularIso (φ : R →ₐ[k] S) :
    rightIndObj φ (regular (k := k) (R := R)) ≅ leftRestrictedRegular φ where
  hom := rightIndRegularHom φ
  inv := rightIndRegularInv φ
  hom_inv_id := by
    apply rightInd_hom_ext φ
    intro s r
    change rightIndRegularInvLinear φ (show S from rightIndRegularHom φ
      (show rightIndObj φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)) =
      (show RightIndType φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)
    trans rightIndRegularInvLinear φ (φ r * (show Sᵐᵒᵖ from s).unop)
    · exact congrArg (rightIndRegularInvLinear φ) (rightIndRegularHom_mk φ s r)
    rw [rightIndRegularInvLinear_apply]
    trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj (regular (k := k) (R := R)))
      (MulOpposite.op (MulOpposite.op (show R from r)) • s) (1:R)
    · rfl
    trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj (regular (k := k) (R := R))) s
      (MulOpposite.op (show R from r) • (show RightObj (regular (k := k) (R := R)) from (1:R)))
    · exact BalancedTensor.balance _ _ _
    change BalancedTensor.mk s (show RightObj (regular (k := k) (R := R)) from (1 * (1 * (show R from r)) : R)) = BalancedTensor.mk s r
    exact congrArg (fun z : R => BalancedTensor.mk s
      (show RightObj (regular (k := k) (R := R)) from z)) (by exact (congrArg (fun z : R => (1:R)*z) (one_mul (show R from r))).trans (one_mul (show R from r)))
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (show S from rightIndRegularHom φ (rightIndRegularInvLinear φ (show S from s))) =
      (show S from s)
    trans (show S from rightIndRegularHom φ (BalancedTensor.mk
      (show AlgebraInduction.Bimod φ.op from MulOpposite.op (show S from s))
      (show RightObj (regular (k := k) (R := R)) from (1:R))))
    · exact congrArg (fun x : RightIndType φ (regular (k := k) (R := R)) =>
        (show S from rightIndRegularHom φ x)) (rightIndRegularInvLinear_apply φ s)
    exact (rightIndRegularHom_mk φ _ _).trans
      (show φ (1:R) * (show S from s) = (show S from s) by rw [map_one, one_mul])

def leftRestrictedRegularIso (φ : R →ₐ[k] S) :
    (leftFunctor (k := k) (R := R) (S := S)).obj (leftRestrictedRegular φ) ≅
      (AlgebraInduction.res φ).obj (ModuleCat.of S S) :=
by
  let X := (leftFunctor (k := k) (R := R) (S := S)).obj (leftRestrictedRegular φ)
  let Z := (AlgebraInduction.res φ).obj (ModuleCat.of S S)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z)
    (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := fun x : X =>
        (show (AlgebraInduction.res φ).obj (ModuleCat.of S S) from x)
      invFun := fun x => x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change φ r * ((show S from x) * 1) = φ r * (show S from x)
        rw [mul_one] }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

abbrev leftEnvelopingMap (φ : R →ₐ[k] S) : Alg k R U →ₐ[k] Alg k S U :=
  Algebra.TensorProduct.map φ (AlgHom.id k Uᵐᵒᵖ)

def leftIndUnit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj (leftIndObj φ M) :=
  ModuleCat.ofHom (X := M) (Y := (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj (leftIndObj φ M))
  { toFun := fun m => BalancedTensor.mk (k := k) (R := R) (S := S)
      (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m)
    map_add' := by intro m n; exact (BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj M) (show AlgebraInduction.Bimod φ from (1:S))).map_add m n
    map_smul' a m := by
      change BalancedTensor.mk (k := k) (R := R) (S := S)
        (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from a • m) =
        (action (k := k) (R := S) (S := U)
          (BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M))
          (leftEnvelopingMap φ a)) _
      induction a using TensorProduct.inductionOn with
      | tmul r u =>
        change BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from (r ⊗ₜ[k] u) • m) =
          (φ r) • (u • BalancedTensor.mk (k := k) (R := R) (S := S)
            (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m))
        trans BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (r • u • (show Obj M from m))
        · exact congrArg (BalancedTensor.mk (k := k) (R := R) (S := S)
            (show AlgebraInduction.Bimod φ from (1:S))) (tmul_smul M r u m)
        exact (AlgebraInduction.unit φ (ModuleCat.of R (Obj M))).hom.map_smul r (u • (show Obj M from m))
      | add a b ha hb =>
        rw [map_add, map_add]
        change BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from (a+b) • m) = _
        exact (congrArg (fun x : M => BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from x)) (add_smul a b m)).trans
          (((BalancedTensor.mk (k := k) (R := R) (S := S) (N := Obj M)
            (show AlgebraInduction.Bimod φ from (1:S))).map_add _ _).trans
              (congrArg₂ (fun x y => x+y) ha hb)) }

@[simp] lemma leftIndUnit_apply (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndUnit φ M m = BalancedTensor.mk (k := k) (R := R) (S := S)
      (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m) := rfl




def leftIndResMap (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    ModuleCat.of R (Obj M) ⟶ (AlgebraInduction.res φ).obj (ModuleCat.of S (Obj N)) :=
  ModuleCat.ofHom (X := ModuleCat.of R (Obj M))
    (Y := (AlgebraInduction.res φ).obj (ModuleCat.of S (Obj N)))
  { toFun := fun m => (show Obj N from f m)
    map_add' := f.hom.map_add
    map_smul' r m := by
      have h := f.hom.map_smul (r ⊗ₜ[k] (1:Uᵐᵒᵖ)) m
      change (show N from f ((r ⊗ₜ[k] (1:Uᵐᵒᵖ)) • (show M from m))) =
        (leftEnvelopingMap φ (r ⊗ₜ[k] (1:Uᵐᵒᵖ))) • (show N from f m) at h
      exact h }

lemma leftIndResMap_right (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) (u : Uᵐᵒᵖ) (m : Obj M) :
    (show Obj N from f (u • m)) = u • (show Obj N from f m) := by
  have h := f.hom.map_smul ((1:R) ⊗ₜ[k] u) m
  change (show N from f (((1:R) ⊗ₜ[k] u) • (show M from m))) =
    leftEnvelopingMap φ ((1:R) ⊗ₜ[k] u) • (show N from f m) at h
  change (show N from f (((1:R) ⊗ₜ[k] u) • (show M from m))) =
    ((1:S) ⊗ₜ[k] u) • (show N from f m)
  simpa only [leftEnvelopingMap, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using h

def leftIndExtendLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M) →ₗ[S] Obj N :=
  (AlgebraInduction.extend φ (leftIndResMap φ f)).hom

lemma leftIndExtendLinear_right (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) (u : Uᵐᵒᵖ) (x) :
    leftIndExtendLinear φ f (u • x) = u • leftIndExtendLinear φ f x := by
  induction x using BalancedTensor.induction_on with
  | h0 => simp only [smul_zero, map_zero]
  | ht s m =>
    change (show S from s) • (show Obj N from f (u • m)) =
      u • ((show S from s) • (show Obj N from f m))
    rw [leftIndResMap_right φ f, smul_comm]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

def leftIndExtend (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    leftIndObj φ M ⟶ N :=
  ofBimoduleHom (leftIndExtendLinear φ f) (leftIndExtendLinear_right φ f) ≫ (reassembleIso N).hom

@[simp] lemma leftIndExtend_mk (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N)
    (s : AlgebraInduction.Bimod φ) (m : Obj M) :
    leftIndExtend φ f (BalancedTensor.mk s m) = (show Obj N from (show S from s) • (show Obj N from f m)) := rfl




lemma leftInd_hom_ext (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    {f g : leftIndObj φ M ⟶ N}
    (h : ∀ (s : AlgebraInduction.Bimod φ) (m : Obj M),
      f (BalancedTensor.mk s m) = g (BalancedTensor.mk s m)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on (k := k) (R := R) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := Obj M) with
  | h0 => exact f.hom.map_zero.trans g.hom.map_zero.symm
  | ht s m => exact h s m
  | ha x y hx hy =>
    exact (f.hom.map_add x y).trans
      ((congrArg₂ (fun x y => x+y) hx hy).trans (g.hom.map_add x y).symm)

def leftIndComparisonHom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M ⟶ leftIndObj φ M :=
  AlgebraInduction.extend (k := k) (R := Alg k R U) (S := Alg k S U)
    (N := M) (P := leftIndObj φ M) (leftEnvelopingMap φ) (leftIndUnit φ M)

def leftIndComparisonInv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndObj φ M ⟶ (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M :=
  leftIndExtend (k := k) (R := R) (S := S) (U := U) φ (M := M)
    (N := (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M)
    (AlgebraInduction.unit (k := k) (R := Alg k R U) (S := Alg k S U)
      (leftEnvelopingMap (U := U) φ) M)

lemma leftIndComparison_inv_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndComparisonInv φ M (leftIndUnit φ M m) =
      AlgebraInduction.unit (k := k) (R := Alg k R U) (S := Alg k S U) (leftEnvelopingMap φ) M m := by
  change (1:S) • (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
    AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m) = _
  exact one_smul _ _

lemma leftIndComparison_hom_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndComparisonHom φ M (AlgebraInduction.unit (k := k) (R := Alg k R U)
      (S := Alg k S U) (leftEnvelopingMap φ) M m) = leftIndUnit φ M m := by
  change (1:Alg k S U) • (show leftIndObj φ M from leftIndUnit φ M m) = _
  exact one_smul _ _

lemma leftIndComparison_hom_inv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndComparisonHom φ M ≫ leftIndComparisonInv φ M = 𝟙 _ := by
  apply (AlgebraInduction.homEquiv (k := k) (R := Alg k R U) (S := Alg k S U)
    (leftEnvelopingMap φ) M _).injective
  ext m
  change leftIndComparisonInv φ M (leftIndComparisonHom φ M
    (AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)) =
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m
  rw [leftIndComparison_hom_unit, leftIndComparison_inv_unit]

lemma leftIndComparison_inv_hom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndComparisonInv φ M ≫ leftIndComparisonHom φ M = 𝟙 _ := by
  apply leftInd_hom_ext φ
  intro s m
  have h := (leftMap (leftIndComparisonHom φ M)).map_smul (show S from s)
    (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)
  change leftIndComparisonHom φ M ((show S from s) •
    (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)) = _
  apply h.trans
  apply Eq.trans (congrArg (fun x : Obj (leftIndObj φ M) => (show S from s) • x)
    (leftIndComparison_hom_unit φ M m))
  change (show S from s) • ((1:Uᵐᵒᵖ) •
    (BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj M) (show AlgebraInduction.Bimod φ from (1:S)) m)) = BalancedTensor.mk s m
  rw [one_smul]
  exact (AlgebraInduction.mk_one_smul φ (ModuleCat.of R (Obj M)) (show S from s) m).symm

def leftIndComparisonIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M ≅ leftIndObj φ M where
  hom := leftIndComparisonHom φ M
  inv := leftIndComparisonInv φ M
  hom_inv_id := leftIndComparison_hom_inv φ M
  inv_hom_id := leftIndComparison_inv_hom φ M

def leftIndComparison (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (leftEnvelopingMap (U := U) φ) ≅ leftIndFunctor φ :=
  NatIso.ofComponents (leftIndComparisonIso φ) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro a m
    change (show Alg k S U from a) • (show leftIndObj φ N from leftIndUnit φ N (f m)) =
      leftIndMap φ f ((show Alg k S U from a) • (show leftIndObj φ M from leftIndUnit φ M m))
    exact ((leftIndMap φ f).hom.map_smul (show Alg k S U from a)
      (show leftIndObj φ M from leftIndUnit φ M m)).symm)

def leftIndUnderlyingComparison (φ : R →ₐ[k] S) :
    leftIndFunctor (U := U) φ ⋙ leftFunctor ≅ leftFunctor ⋙ AlgebraInduction.functor φ :=
  NatIso.ofComponents (leftIndUnderlyingIso φ) (by intro M N f; ext x; rfl)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev leftComplex (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) :=
  ((leftFunctor (k := k) (R := R) (S := S)).mapHomologicalComplex (.down ℕ)).obj P
abbrev rightComplex (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) :=
  ((rightFunctor (k := k) (R := R) (S := S)).mapHomologicalComplex (.down ℕ)).obj P

def leftCokerEquiv (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n)) ≃ₗ[R] NatCoker.C (leftComplex P) n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightCokerEquiv (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n)) ≃ₗ[Sᵐᵒᵖ] NatCoker.C (rightComplex P) n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma coker_left_projective_of_homotopy (P : ChainComplex (ModuleCat (Alg k R S)) ℕ)
    (Q : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (e : HomotopyEquiv (leftComplex P) Q)
    [Subsingleton (Q.X (n+1))] [Module.Projective R (Obj (P.X n))] :
    Module.Projective R (Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n))) := by
  let : Module.Projective R ((leftComplex P).X n) :=
    inferInstanceAs (Module.Projective R (Obj (P.X n)))
  let := NatCoker.projective_of_homotopy (leftComplex P) n e
  exact Module.Projective.of_equiv (leftCokerEquiv P n).symm

lemma coker_right_projective_of_homotopy (P : ChainComplex (ModuleCat (Alg k R S)) ℕ)
    (Q : ChainComplex (ModuleCat Sᵐᵒᵖ) ℕ) (n : ℕ) (e : HomotopyEquiv (rightComplex P) Q)
    [Subsingleton (Q.X (n+1))] [Module.Projective Sᵐᵒᵖ (Obj (P.X n))] :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n))) := by
  let : Module.Projective Sᵐᵒᵖ ((rightComplex P).X n) :=
    inferInstanceAs (Module.Projective Sᵐᵒᵖ (Obj (P.X n)))
  let := NatCoker.projective_of_homotopy (rightComplex P) n e
  exact Module.Projective.of_equiv (rightCokerEquiv P n).symm

end Tachikawa.Enveloping

namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C]

def transportResolution {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) :
    ProjectiveResolution N where
  complex := P.complex
  projective n := P.projective n
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := inferInstance

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma rightInducedResolution_finite (φ : R →ₐ[k] S) (n : ℕ) :
    Module.Finite (Alg k R S) ((rightInducedResolution φ).complex.X n) := by
  change Module.Finite (Alg k R S)
    ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  exact Module.Finite.of_restrictScalars_finite k _ _

def rightInducedLeftResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S)) :=
  Tachikawa.transportResolution
    (leftResolutionOf (rightInducedResolution φ) (rightInducedResolution_finite φ))
    ((leftFunctor (k := k) (R := R) (S := S)).mapIso
      ((rightIndComparisonIso φ (regular (k := k) (R := R))) ≪≫ rightIndRegularIso φ) ≪≫
      leftRestrictedRegularIso φ)

def inducedFactorIso (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (rightEnvelopingMap (U := R) φ) ⋙
      AlgebraInduction.functor (leftEnvelopingMap (U := S) φ) ≅
      AlgebraInduction.functor (envelopingMap φ) :=
  AlgebraInduction.compositionIso _ _ ≪≫ eqToIso (by
    congr 1
    ext a <;> rfl)

def inducedLeftComplexIso (φ : R →ₐ[k] S) :
    leftComplex (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ).mapHomologicalComplex _).obj
        (rightInducedLeftResolution φ).complex := by
  let P := (regularResolution (k := k) (R := R)).complex
  let J := AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)
  let L := AlgebraInduction.functor (leftEnvelopingMap (U := S) φ)
  let U := leftFunctor (k := k) (R := S) (S := S)
  let V := leftFunctor (k := k) (R := R) (S := S)
  let I := AlgebraInduction.functor φ
  let a : L ⋙ U ≅ V ⋙ I :=
    Functor.isoWhiskerRight (leftIndComparison (U := S) φ) U ≪≫
      leftIndUnderlyingComparison (U := S) φ
  let b := Functor.isoWhiskerRight (inducedFactorIso φ) U
  exact (NatIso.mapHomologicalComplex b _).symm.app P ≪≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft J a) _).app P

def inducedLeftHomotopy (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S))) :
    HomotopyEquiv (leftComplex (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj Q.complex) :=
  (HomotopyEquiv.ofIso (inducedLeftComplexIso φ)).trans
    ((AlgebraInduction.functor φ).mapHomotopyEquiv
      (ProjectiveResolution.homotopyEquiv (rightInducedLeftResolution φ) Q))

lemma inducedCoker_left_projective (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S)))
    (n : ℕ) (hn : CategoryTheory.Limits.IsZero (Q.complex.X (n+1))) :
    Module.Projective S (Obj (ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) n))) := by
  let I := AlgebraInduction.functor φ
  let C := (I.mapHomologicalComplex _).obj Q.complex
  have hC : CategoryTheory.Limits.IsZero (C.X (n+1)) := I.map_isZero hn
  let : Subsingleton (C.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hC
  exact coker_left_projective_of_homotopy (inducedRegularComplex φ) C n (inducedLeftHomotopy φ Q)

end Tachikawa.Enveloping


end
end OAI
