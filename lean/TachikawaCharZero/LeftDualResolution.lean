import TachikawaCharZero.Dual
import TachikawaCharZero.TwistedTrace
import TachikawaCharZero.ProjectivePackaging
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-! A length-two projective resolution of DC as a left C-module over Q.
The sparse generators follow OpenAI Math's ReverseResolution.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The middle map has the characteristic-zero sign x - y/4. -/
namespace TachikawaCharZero.Resolution
noncomputable section
open OAI.ArExplicit
open CategoryTheory

def dualCoeff (i : Letter) : Dual where
  toFun a := a.coeff i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def leftDualZ : Ce →ₗ[A] Dual where
  toFun a := (a:A) • dualCoeff .z
  map_add' a b := add_smul (a:A) (b:A) _
  map_smul' r a := mul_smul r (a:A) _

def leftDualJ : Ce →ₗ[A] Dual where
  toFun a := (a:A) • dualCoeff .j
  map_add' a b := add_smul (a:A) (b:A) _
  map_smul' r a := mul_smul r (a:A) _

def leftDualAug : (Ce × Ce) →ₗ[A] Dual := leftDualZ.coprod leftDualJ

theorem leftDualAug_apply (x y : V) (a : A) :
    leftDualAug (ceIso x,ceIso y) a =
      a.coeff .e*x 3 + a.coeff .z*x 0 + 2*a.coeff .x*x 2 + a.coeff .y*x 1 +
      2*a.coeff .v*x 4 + a.coeff .u*x 5 +
      (a.coeff .f*y 5 + a.coeff .j*y 0 + a.coeff .t*y 1 +
        4*a.coeff .t*y 2 + 2*a.coeff .n*y 4) := by
  change (a*ceEmbed x).coeff .z + (a*ceEmbed y).coeff .j = _
  norm_num [BaseAlgebra.product,ceEmbed]

theorem leftDualAug_surjective : Function.Surjective leftDualAug := by
  intro φ
  let b (i : Letter) : ℚ := φ (BaseAlgebra.basisVector 2 i)
  refine ⟨(ceIso ![b .z,b .y,b .x/2,b .e,b .v/2,b .u],
    ceIso ![b .j,b .t,0,0,b .n/2,b .f]), ?_⟩
  apply (coordinateBasis (2:ℚ)).ext
  intro i
  change leftDualAug _ (coordinateBasis (2:ℚ) i) = φ (coordinateBasis (2:ℚ) i)
  rw [coordinateBasis_apply,leftDualAug_apply]
  cases i <;> simp [BaseAlgebra.basisVector,b]
  all_goals ring

def leftDualD1 : Ce →ₗ[A] (Ce × Ce) :=
  (0 : Ce →ₗ[A] Ce).prod (ceDiff (1/4))

theorem leftDualD1_iso (a : V) :
    leftDualD1 (ceIso a) = (ceIso 0,ceIso (rightD (1/4) a)) := by
  change (0,ceDiff (1/4) (ceIso a)) = _
  rw [ceIso.map_zero,ceDiff_iso]

theorem t_fixed_by_e : BaseAlgebra.basisVector (2:ℚ) .t * vertexE =
    BaseAlgebra.basisVector (2:ℚ) .t := BaseAlgebra.basis_mul 2 .t .e

def rhoT : Cf →ₗ[A] Ce := Corner.mulRight
  (BaseAlgebra.basisVector 2 .t) t_fixed_by_e

theorem rhoT_iso (a : V₀) :
    rhoT (cfIso a) = ceIso ![0,2*a 1,a 1,2*a 2,a 0,2*a 3] := by
  apply Subtype.ext
  change cfEmbed a * BaseAlgebra.basisVector 2 .t = ceEmbed _
  ext i
  cases i <;> simp [cfEmbed,ceEmbed,BaseAlgebra.product]

theorem leftDualAug_kernel (x y : V) :
    leftDualAug (ceIso x,ceIso y) = 0 ↔
      x = 0 ∧ y 0 = 0 ∧ y 1+4*y 2 = 0 ∧ y 4 = 0 ∧ y 5 = 0 := by
  constructor
  · intro hh
    have h (i : Letter) := congrArg (fun ψ : Dual => ψ (BaseAlgebra.basisVector 2 i)) hh
    have hx0 : x 0=0 := by simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .z
    have hx1 : x 1=0 := by simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .y
    have hx2 : x 2=0 := by simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .x
    have hx3 : x 3=0 := by simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .e
    have hx4 : x 4=0 := by simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .v
    have hx5 : x 5=0 := by simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .u
    refine ⟨?_,?_,?_,?_,?_⟩
    · ext i; fin_cases i <;> simp [hx0,hx1,hx2,hx3,hx4,hx5]
    · simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .j
    · simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .t
    · simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .n
    · simpa [leftDualAug_apply,BaseAlgebra.basisVector] using h .f
  · rintro ⟨rfl,h0,h12,h4,h5⟩
    apply dual_ext
    intro a
    rw [leftDualAug_apply,dual_zero_apply]
    have h1 : y 1 = -4*y 2 := by linarith
    simp [h0,h1,h4,h5]
    ring

theorem leftDualAug_exact : Function.Exact leftDualD1 leftDualAug := by
  rintro ⟨x,y⟩
  obtain ⟨x,rfl⟩ := ceIso.surjective x
  obtain ⟨y,rfl⟩ := ceIso.surjective y
  constructor
  · intro hh
    obtain ⟨rfl,h0,h12,h4,h5⟩ := (leftDualAug_kernel x y).mp hh
    refine ⟨ceIso ![y 1,0,y 3,0,0,0], ?_⟩
    rw [leftDualD1_iso]
    apply Prod.ext
    · rfl
    · apply ceIso.injective.eq_iff.mpr
      have h2 : y 2 = -(1/4)*y 1 := by linarith
      ext i
      fin_cases i <;> norm_num [rightD,h0,h2,h4,h5]
  · rintro ⟨z,hz⟩
    obtain ⟨z,rfl⟩ := ceIso.surjective z
    rw [← hz,leftDualD1_iso,leftDualAug_kernel]
    norm_num [rightD]
    ring

theorem rhoT_injective : Function.Injective rhoT := by
  intro a b h
  obtain ⟨a,rfl⟩ := cfIso.surjective a
  obtain ⟨b,rfl⟩ := cfIso.surjective b
  rw [rhoT_iso,rhoT_iso] at h
  have hc := ceIso.injective h
  apply cfIso.injective.eq_iff.mpr
  have h0 := congrFun hc 4
  have h1 := congrFun hc 2
  have h2 := congrFun hc 3
  have h3 := congrFun hc 5
  change a 0=b 0 at h0
  change a 1=b 1 at h1
  change 2*a 2=2*b 2 at h2
  change 2*a 3=2*b 3 at h3
  ext i
  fin_cases i
  · change a 0=b 0
    exact h0
  · change a 1=b 1
    exact h1
  · change a 2=b 2
    linarith only [h2]
  · change a 3=b 3
    linarith only [h3]

theorem rhoT_exact : Function.Exact rhoT (ceDiff (1/4)) := by
  intro a
  obtain ⟨a,rfl⟩ := ceIso.surjective a
  constructor
  · intro h
    rw [ceDiff_iso,← ceIso.map_zero] at h
    have hh := ceIso.injective h
    have h0 : a 0=0 := by have hh' := congrFun hh 1; simpa [rightD] using hh'
    have h1 : 2*a 2=a 1 := by
      have hh' := congrFun hh 3
      norm_num [rightD] at hh'
      linarith
    refine ⟨cfIso ![a 4,a 2,a 3/2,a 5/2], ?_⟩
    rw [rhoT_iso]
    apply ceIso.injective.eq_iff.mpr
    ext i
    fin_cases i <;> simp [h0,h1]
    all_goals ring
  · rintro ⟨b,hb⟩
    obtain ⟨b,rfl⟩ := cfIso.surjective b
    rw [← hb,rhoT_iso,ceDiff_iso,← ceIso.map_zero]
    apply congrArg ceIso
    ext i
    fin_cases i <;> norm_num [rightD]
    ring

def leftDualResObj : ℕ → ModuleCat A
  | 0 => ModuleCat.of A (Ce × Ce)
  | 1 => ModuleCat.of A Ce
  | 2 => ModuleCat.of A Cf
  | _+3 => ModuleCat.of A PUnit

def leftDualResD : ∀ n, leftDualResObj (n+1) ⟶ leftDualResObj n
  | 0 => ModuleCat.ofHom leftDualD1
  | 1 => ModuleCat.ofHom rhoT
  | _+2 => 0

theorem leftDualResD_exact (n : ℕ) :
    Function.Exact (leftDualResD (n+1)) (leftDualResD n) := by
  rcases n with _ | _ | _ | n
  · change Function.Exact rhoT leftDualD1
    intro a
    change (0,ceDiff (1/4) a)=(0,0) ↔ _
    rw [Prod.mk.injEq]
    simpa only [true_and] using rhoT_exact a
  · change Function.Exact (fun _ : PUnit => (0:Cf)) rhoT
    intro a
    constructor
    · intro h
      exact ⟨PUnit.unit,(rhoT_injective (h.trans (map_zero rhoT).symm)).symm⟩
    · rintro ⟨_,rfl⟩
      exact map_zero rhoT
  · change Function.Exact (fun _ : PUnit => (0:PUnit)) (fun _ : PUnit => (0:Cf))
    intro a
    exact ⟨fun _ => ⟨PUnit.unit,Subsingleton.elim _ _⟩,fun _ => rfl⟩
  · change Function.Exact (fun _ : PUnit => (0:PUnit)) (fun _ : PUnit => (0:PUnit))
    intro a
    exact ⟨fun _ => ⟨PUnit.unit,Subsingleton.elim _ _⟩,fun _ => rfl⟩

def leftDualProjectiveResolution : ProjectiveResolution (ModuleCat.of A Dual) :=
  resolutionOfExact _ leftDualResObj leftDualResD (ModuleCat.ofHom leftDualAug)
    leftDualResD_exact leftDualAug_exact leftDualAug_surjective
    (fun n => by rcases n with _ | _ | _ | n <;> dsimp [leftDualResObj] <;> infer_instance)

theorem leftDual_projectiveDimension :
    HasProjectiveDimensionLE (ModuleCat.of A Dual) 2 := by
  let P := leftDualProjectiveResolution
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f,hf,rfl⟩ := P.extMk_surjective α (i+1) rfl
  have hs : Subsingleton (P.complex.X i) := by
    change Subsingleton (leftDualResObj i)
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_comm 3 n]
    exact inferInstanceAs (Subsingleton PUnit)
  have h : f=0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [hs.elim x 0]
    exact map_zero _
  subst f
  exact P.extMk_zero _ _

end
end TachikawaCharZero.Resolution
