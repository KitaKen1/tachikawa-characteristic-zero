import OAI.RingTheory.Tachikawa.Coresolution
import OAI.RingTheory.Tachikawa.NakayamaTransfer

/-! Generic dualization of projective resolutions, extracted from OpenAI Math
FiniteCoinduction.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0). Excerpt declarations are unchanged. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def LeftDual (M : ModuleCat Rᵐᵒᵖ) := Module.Dual k M
namespace LeftDual
variable {M N : ModuleCat Rᵐᵒᵖ}
instance : AddCommGroup (LeftDual (k := k) M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance : Module k (LeftDual (k := k) M) := inferInstanceAs (Module k (Module.Dual k M))
instance : FunLike (LeftDual (k := k) M) M k := inferInstanceAs (FunLike (Module.Dual k M) M k)
instance : LinearMapClass (LeftDual (k := k) M) k M k := inferInstanceAs (LinearMapClass (Module.Dual k M) k M k)
@[ext] lemma ext {φ ψ : LeftDual (k := k) M} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h
instance : Module R (LeftDual (k := k) M) where
  smul r φ := φ.comp (DistribSMul.toLinearMap k M (MulOpposite.op r))
  one_smul φ := by ext x; change φ ((1 : Rᵐᵒᵖ) • x) = φ x; simp
  mul_smul a b φ := by ext x; change φ (MulOpposite.op (a*b) • x) = φ (MulOpposite.op b • MulOpposite.op a • x); simp [mul_smul]
  smul_zero r := by ext x; rfl
  smul_add r φ ψ := by ext x; rfl
  add_smul r s φ := by ext x; change φ (MulOpposite.op (r+s) • x) = φ (MulOpposite.op r • x) + φ (MulOpposite.op s • x); simp [add_smul]
  zero_smul φ := by ext x; change φ ((0 : Rᵐᵒᵖ) • x) = 0; simp
@[simp] lemma smul_apply (r : R) (φ : LeftDual (k := k) M) (x : M) : (r • φ) x = φ (MulOpposite.op r • x) := rfl
instance : IsScalarTower k R (LeftDual (k := k) M) where
  smul_assoc c r φ := by ext x; change φ (MulOpposite.op (c • r) • x) = c • φ (MulOpposite.op r • x); simp [smul_assoc]
instance : SMulCommClass k R (LeftDual (k := k) M) where
  smul_comm c r φ := by ext x; rfl
instance [FiniteDimensional k M] : FiniteDimensional k (LeftDual (k := k) M) := inferInstanceAs (FiniteDimensional k (Module.Dual k M))

def map (f : M ⟶ N) : LeftDual (k := k) N →ₗ[R] LeftDual (k := k) M where
  toFun φ := φ.comp (f.hom.restrictScalars k)
  map_add' _ _ := rfl
  map_smul' r φ := by ext x; change φ (MulOpposite.op r • f x) = φ (f (MulOpposite.op r • x)); rw [f.hom.map_smul]
@[simp] lemma map_apply (f : M ⟶ N) (φ : LeftDual (k := k) N) (x : M) : map f φ x = φ (f x) := rfl
lemma exact {P : ModuleCat Rᵐᵒᵖ} (f : M ⟶ N) (g : N ⟶ P) (h : Function.Exact f g) : Function.Exact (map (k := k) g) (map (k := k) f) :=
  exact_dual (f.hom.restrictScalars k) (g.hom.restrictScalars k) h
lemma map_injective (f : M ⟶ N) (h : Function.Surjective f) : Function.Injective (map (k := k) f) := by
  intro φ ψ he
  ext x
  obtain ⟨y,rfl⟩ := h x
  exact congrArg (fun a : LeftDual (k := k) M => a y) he
end LeftDual

def RightDual (M : ModuleCat R) := Module.Dual k M
namespace RightDual
variable {M N : ModuleCat R}
instance : AddCommGroup (RightDual (k := k) M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance : Module k (RightDual (k := k) M) := inferInstanceAs (Module k (Module.Dual k M))
instance : FunLike (RightDual (k := k) M) M k := inferInstanceAs (FunLike (Module.Dual k M) M k)
instance : LinearMapClass (RightDual (k := k) M) k M k := inferInstanceAs (LinearMapClass (Module.Dual k M) k M k)
@[ext] lemma ext {φ ψ : RightDual (k := k) M} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h
instance : Module Rᵐᵒᵖ (RightDual (k := k) M) where
  smul r φ := φ.comp (DistribSMul.toLinearMap k M r.unop)
  one_smul φ := by ext x; change φ ((1 : R) • x) = φ x; simp
  mul_smul a b φ := by ext x; change φ ((b.unop*a.unop) • x) = φ (b.unop • a.unop • x); rw [mul_smul]
  smul_zero r := by ext x; rfl
  smul_add r φ ψ := by ext x; rfl
  add_smul r s φ := by ext x; change φ ((r.unop+s.unop) • x) = φ (r.unop • x) + φ (s.unop • x); simp [add_smul]
  zero_smul φ := by ext x; change φ ((0 : R) • x) = 0; simp
@[simp] lemma smul_apply (r : Rᵐᵒᵖ) (φ : RightDual (k := k) M) (x : M) : (r • φ) x = φ (r.unop • x) := rfl
instance : IsScalarTower k Rᵐᵒᵖ (RightDual (k := k) M) where
  smul_assoc c r φ := by ext x; change φ ((c • r.unop) • x) = c • φ (r.unop • x); simp [smul_assoc]
instance : SMulCommClass k Rᵐᵒᵖ (RightDual (k := k) M) where
  smul_comm c r φ := by ext x; rfl

def map (f : M ⟶ N) : RightDual (k := k) N →ₗ[Rᵐᵒᵖ] RightDual (k := k) M where
  toFun φ := φ.comp (f.hom.restrictScalars k)
  map_add' _ _ := rfl
  map_smul' r φ := by ext x; change φ (r.unop • f x) = φ (f (r.unop • x)); rw [f.hom.map_smul]
@[simp] lemma map_apply (f : M ⟶ N) (φ : RightDual (k := k) N) (x : M) : map f φ x = φ (f x) := rfl
lemma map_surjective (f : M ⟶ N) (h : Function.Injective f) : Function.Surjective (map (k := k) f) :=
  LinearMap.dualMap_surjective_of_injective h
end RightDual




def dualTranspose {M : ModuleCat R} {P : ModuleCat Rᵐᵒᵖ}
    (g : M →ₗ[R] LeftDual (k := k) P) : P →ₗ[Rᵐᵒᵖ] RightDual (k := k) M where
  toFun p :=
    { toFun := fun x => g x p
      map_add' x y := by change g (x+y) p = g x p + g y p; rw [g.map_add]; rfl
      map_smul' c x := by
        change g (c • x) p = c • g x p
        exact congrArg (fun φ : LeftDual (k := k) P => φ p)
          ((g.restrictScalars k).map_smul c x) }
  map_add' p q := by ext x; exact (g x).map_add p q
  map_smul' r p := by
    ext x
    change g x (r • p) = g (r.unop • x) p
    rw [g.map_smul]
    rfl

def dualUntranspose {M : ModuleCat R} {P : ModuleCat Rᵐᵒᵖ}
    (g : P →ₗ[Rᵐᵒᵖ] RightDual (k := k) M) : M →ₗ[R] LeftDual (k := k) P where
  toFun x :=
    { toFun := fun p => g p x
      map_add' p q := by change g (p+q) x = g p x + g q x; rw [g.map_add]; rfl
      map_smul' c p := by
        change g (c • p) x = c • g p x
        exact congrArg (fun φ : RightDual (k := k) M => φ x)
          ((g.restrictScalars k).map_smul c p) }
  map_add' x y := by ext p; exact (g p).map_add x y
  map_smul' r x := by
    ext p
    change g p (r • x) = g (MulOpposite.op r • p) x
    rw [g.map_smul]
    rfl

instance leftDual_injective (P : ModuleCat Rᵐᵒᵖ) [Module.Projective Rᵐᵒᵖ P] :
    Module.Injective R (LeftDual (k := k) P) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let X' : ModuleCat R := ModuleCat.of R X
    let Y' : ModuleCat R := ModuleCat.of R Y
    let f' : X' ⟶ Y' := ModuleCat.ofHom f
    let g' : X' →ₗ[R] LeftDual (k := k) P := g
    obtain ⟨h,hh⟩ := Module.projective_lifting_property (RightDual.map (k := k) f')
      (dualTranspose g') (RightDual.map_surjective f' hf)
    refine ⟨dualUntranspose (M := Y') h, ?_⟩
    intro x
    apply LeftDual.ext
    intro p
    exact congrArg (fun φ : RightDual (k := k) X' => φ x) (LinearMap.congr_fun hh p)

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def leftDualObj (M : ModuleCat Rᵐᵒᵖ) : ModuleCat R := ModuleCat.of R (LeftDual (k := k) M)

def dualResolution {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M) :
    InjectiveResolution (leftDualObj (k := k) M) := by
  let J (n : ℕ) := leftDualObj (k := k) (P.complex.X n)
  let d (n : ℕ) : J n ⟶ J (n+1) := ModuleCat.ofHom (LeftDual.map (P.complex.d (n+1) n))
  let ε : leftDualObj (k := k) M ⟶ J 0 := ModuleCat.ofHom (LeftDual.map (P.π.f 0))
  apply coresolutionOfExact _ J d ε
  · intro n
    exact LeftDual.exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (P.exact_succ n))
  · exact LeftDual.exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 P.exact₀)
  · have hπ := (ModuleCat.epi_iff_surjective (P.π.f 0)).1 inferInstance
    exact LeftDual.map_injective _ hπ
  · intro n
    let : Projective (P.complex.X n) := P.projective n
    let : Module.Projective Rᵐᵒᵖ (P.complex.X n) := inferInstance
    exact Module.injective_object_of_injective_module R (LeftDual (k := k) (P.complex.X n))

lemma leftDualObj_isZero {M : ModuleCat Rᵐᵒᵖ} (hM : IsZero M) :
    IsZero (leftDualObj (k := k) M) := by
  have hm (x : M) : x = 0 := by
    have h := hM.eq_of_src (𝟙 M) 0
    exact congrArg (fun f : M ⟶ M => f x) h
  have : Subsingleton (LeftDual (k := k) M) := by
    constructor
    intro φ ψ
    apply LeftDual.ext
    intro x
    rw [hm x]
    exact map_zero φ |>.trans (map_zero ψ).symm
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (LeftDual (k := k) M))

lemma dualResolution_above {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) (n : ℕ) (hn : d < n) :
    IsZero ((dualResolution (k := k) P).cocomplex.X n) :=
  leftDualObj_isZero (h n hn)

lemma dualResolution_ext_zero {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) (X : ModuleCat R) (n : ℕ) (hn : d < n) :
    Subsingleton (Abelian.Ext X (leftDualObj (k := k) M) n) := by
  have hz (α : Abelian.Ext X (leftDualObj (k := k) M) n) : α = 0 := by
    obtain ⟨f,hf,rfl⟩ := (dualResolution (k := k) P).extMk_surjective α (n+1) rfl
    have hzero := (dualResolution_above P d h n hn).eq_of_tgt f 0
    subst f
    exact (dualResolution (k := k) P).extMk_zero _ _
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end Tachikawa

end
end OAI
