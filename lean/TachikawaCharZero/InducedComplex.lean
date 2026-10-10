import TachikawaCharZero.TrivialCorners
import TachikawaCharZero.HomDual
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-! The actual induced projective complex over T=C⋉DC, using corners.
The first coordinates are the previously verified C-resolution; the second
coordinates are the rational dual of the verified right-corner Hom complex.
Exactness is proved in every degree except the degree-two defect. -/
namespace TachikawaCharZero.Induced
noncomputable section
open Resolution CategoryTheory OAI.ArExplicit

abbrev TE := corner vertexE
abbrev TF := corner vertexF
def decompE := decomp vertexE_idempotent
def decompF := decomp vertexF_idempotent
instance teProjective : Module.Projective T TE := projective vertexE_idempotent
instance tfProjective : Module.Projective T TF := projective vertexF_idempotent

def teDiff (t : ℚ) : TE →ₗ[T] TE := differential (ell t) (ell_mem t)
def tiMap : TE →ₗ[T] TF := differential (BaseAlgebra.basisVector 2 .u) u_fixed_by_f
def nuDiff (t : ℚ) := ((leftDiff t).restrictScalars ℚ).dualMap
def nuInitial := (leftInitial.restrictScalars ℚ).dualMap

theorem teDiff_decomp (t : ℚ) (a : TE) :
    decompE (teDiff t a)=(ceDiff t (decompE a).1,nuDiff t (decompE a).2) :=
  decomp_differential vertexE_idempotent vertexE_idempotent
    (ell t) (e_fixed_ell t) (ell_mem t) a

theorem tiMap_decomp (a : TE) :
    decompF (tiMap a)=(initialMap (decompE a).1,nuInitial (decompE a).2) :=
  decomp_differential vertexE_idempotent vertexF_idempotent
    _ e_fixed_u u_fixed_by_f a

theorem teDiff_sq (t : ℚ) (a : TE) : teDiff t (teDiff (-2*t) a)=0 := by
  have h : ell (-2*t)*ell t=0 := by
    ext i
    cases i <;> simp [ell,BaseAlgebra.product]
  apply Subtype.ext
  change ((a:T)*TrivSqZeroExt.inl (ell (-2*t)))*TrivSqZeroExt.inl (ell t)=0
  rw [mul_assoc,TrivSqZeroExt.inl_mul_inl,h,TrivSqZeroExt.inl_zero,mul_zero]

theorem tiMap_sq (a : TE) : tiMap (teDiff 1 a)=0 := by
  have h : ell 1*BaseAlgebra.basisVector 2 .u=0 := by
    ext i
    cases i <;> simp [ell,BaseAlgebra.product]
  apply Subtype.ext
  change ((a:T)*TrivSqZeroExt.inl (ell 1))*TrivSqZeroExt.inl (BaseAlgebra.basisVector 2 .u)=0
  rw [mul_assoc,TrivSqZeroExt.inl_mul_inl,h,TrivSqZeroExt.inl_zero,mul_zero]

theorem exact_product_transfer
    {U V W U₁ U₂ V₁ V₂ W₁ W₂ : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [AddCommGroup U₁] [Module ℚ U₁]
    [AddCommGroup U₂] [Module ℚ U₂] [AddCommGroup V₁] [Module ℚ V₁]
    [AddCommGroup V₂] [Module ℚ V₂] [AddCommGroup W₁] [Module ℚ W₁]
    [AddCommGroup W₂] [Module ℚ W₂]
    (eU : U ≃ₗ[ℚ] U₁×U₂) (eV : V ≃ₗ[ℚ] V₁×V₂) (eW : W ≃ₗ[ℚ] W₁×W₂)
    (f : U → V) (g : V → W) (f₁ : U₁ → V₁) (f₂ : U₂ → V₂)
    (g₁ : V₁ → W₁) (g₂ : V₂ → W₂)
    (hf : ∀ u, eV (f u)=(f₁ (eU u).1,f₂ (eU u).2))
    (hg : ∀ v, eW (g v)=(g₁ (eV v).1,g₂ (eV v).2))
    (h₁ : Function.Exact f₁ g₁) (h₂ : Function.Exact f₂ g₂) : Function.Exact f g := by
  intro v
  constructor
  · intro hv
    have hz : (g₁ (eV v).1,g₂ (eV v).2)=0 := by rw [← hg,hv,map_zero]
    obtain ⟨u₁,hu₁⟩ := (h₁ (eV v).1).mp (congrArg Prod.fst hz)
    obtain ⟨u₂,hu₂⟩ := (h₂ (eV v).2).mp (congrArg Prod.snd hz)
    refine ⟨eU.symm (u₁,u₂),eV.injective ?_⟩
    rw [hf,eU.apply_symm_apply,hu₁,hu₂]
  · rintro ⟨u,rfl⟩
    apply eW.injective
    rw [hg,hf,map_zero]
    exact Prod.ext (h₁.apply_apply_eq_zero _) (h₂.apply_apply_eq_zero _)

theorem teDiff_exact_all_degrees (m : ℕ) :
    Function.Exact (teDiff ((-2:ℚ)^(m+2))) (teDiff ((-2:ℚ)^(m+1))) :=
  exact_product_transfer decompE decompE decompE _ _ _ _ _ _
    (teDiff_decomp _) (teDiff_decomp _) (ceDiff_exact_all_degrees (m+1))
    (exact_dual _ _ (left_exact_all_degrees m))

theorem tiMap_exact : Function.Exact (teDiff 1) tiMap :=
  exact_product_transfer decompE decompE decompF _ _ _ _ _ _
    (teDiff_decomp 1) tiMap_decomp initial_exact (exact_dual _ _ leftInitial_exact)

def characterT : T →ₐ[ℚ] ℚ := character.comp (TrivSqZeroExt.fstHom ℚ A Dual)
def S := ℚ
instance : AddCommGroup S := inferInstanceAs (AddCommGroup ℚ)
instance : Module ℚ S := inferInstanceAs (Module ℚ ℚ)
instance : Module T S := Module.compHom S characterT.toRingHom
instance : IsScalarTower ℚ T S := IsScalarTower.of_algebraMap_smul fun c x => by
  change characterT (algebraMap ℚ T c) • x=c • x
  rw [AlgHom.commutes]
  rfl
instance : Module.Finite ℚ S := inferInstanceAs (Module.Finite ℚ ℚ)

def aug : TF →ₗ[T] S where
  toFun a := (a:T).fst.coeff .f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem aug_surjective : Function.Surjective aug := by
  intro x
  exact ⟨decompF.symm (cfIso ![(show ℚ from x),0,0,0],0),rfl⟩

theorem aug_exact : Function.Exact tiMap aug := by
  intro a
  constructor
  · intro ha
    have hc : characterAug (decompF a).1=0 := ha
    obtain ⟨c,hc⟩ := (characterAug_exact _).mp hc
    obtain ⟨ψ,hψ⟩ := LinearMap.dualMap_surjective_of_injective
      (f := leftInitial.restrictScalars ℚ) leftInitial_injective
      (decompF a).2
    refine ⟨decompE.symm (c,ψ),decompF.injective ?_⟩
    rw [tiMap_decomp,decompE.apply_symm_apply]
    exact Prod.ext hc hψ
  · rintro ⟨b,rfl⟩
    have h := characterAug_exact.apply_apply_eq_zero (decompE b).1
    exact h

def obj : ℕ → ModuleCat T
  | 0 => ModuleCat.of T TF
  | _+1 => ModuleCat.of T TE

def d : ∀ n, obj (n+1) ⟶ obj n
  | 0 => ModuleCat.ofHom tiMap
  | n+1 => ModuleCat.ofHom (teDiff ((-2:ℚ)^n))

theorem d_sq (n : ℕ) : d (n+1) ≫ d n=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  cases n with
  | zero => exact tiMap_sq a
  | succ n =>
    change teDiff ((-2:ℚ)^n) (teDiff ((-2:ℚ)^(n+1)) a)=0
    rw [pow_succ']
    exact teDiff_sq _ a

def complex : ChainComplex (ModuleCat T) ℕ := ChainComplex.of obj d d_sq

theorem obj_projective (n : ℕ) : Projective (obj n) := by
  cases n <;> dsimp [obj] <;> infer_instance

theorem d_exact (n : ℕ) (hn : n≠1) : Function.Exact (d (n+1)) (d n) := by
  rcases n with _ | _ | m
  · exact tiMap_exact
  · exact (hn rfl).elim
  · exact teDiff_exact_all_degrees m

theorem e_smul_S (x : S) : (TrivSqZeroExt.inl vertexE : T) • x=0 := by
  change (0:ℚ) • (show ℚ from x)=0
  exact zero_smul ℚ _

theorem homTE_zero (F : TE →ₗ[T] S) : F=0 := by
  let hp : (TrivSqZeroExt.inl vertexE:T)*TrivSqZeroExt.inl vertexE=TrivSqZeroExt.inl vertexE := by
    rw [TrivSqZeroExt.inl_mul_inl,vertexE_idempotent]
  let e : TE := ⟨TrivSqZeroExt.inl vertexE,hp⟩
  have he : (TrivSqZeroExt.inl vertexE:T) • e=e := Subtype.ext hp
  have hF : F e=0 := by rw [← he,F.map_smul,e_smul_S]
  apply LinearMap.ext
  intro a
  change F a=0
  have ha : (a:T) • e=a := Subtype.ext a.property
  rw [← ha,F.map_smul,hF,smul_zero]

end
end TachikawaCharZero.Induced
