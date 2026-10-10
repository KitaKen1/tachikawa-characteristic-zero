import TachikawaCharZero.ScalingSocle
import TachikawaCharZero.TensorDualResolution
import TachikawaCharZero.RightDualDimension
import OAI.RingTheory.Tachikawa.ProductResolution
import OAI.RingTheory.Tachikawa.RestrictedRegular
import OAI.RingTheory.Tachikawa.GenericCoinduction

/-! Actual rational finite resolutions of the regular trivial extension
restricted to C, on both sides. Tensoring these length-two resolutions
constructs the restriction bounds. Generic product resolution arguments
are reused unchanged from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.RestrictionDimension
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
abbrev A := Resolution.A
abbrev T := Starting.T
abbrev B := Starting.B
abbrev E := Starting.E
abbrev BE := ScalingSocle.BE
abbrev EE := ScalingSocle.EE
open ScalingSocle (inclusionC inclusionB inclusionBE restriction)
open TensorDualResolution (transportResolution total_isZero_above)

section Generic
variable {k R U S V : Type} [Field k] [Ring R] [Ring U] [Ring S] [Ring V]
  [Algebra k R] [Algebra k U] [Algebra k S] [Algebra k V]

def tensorRegularUnderlying (φ : R →ₐ[k] S) (ψ : U →ₐ[k] V) :
    OuterTensor.Obj k R U
      ((AlgebraInduction.res φ).obj (ModuleCat.of S S))
      ((AlgebraInduction.res ψ).obj (ModuleCat.of V V)) ≃ₗ[k] S ⊗[k] V :=
  TensorProduct.congr (Enveloping.resRegularUnderlying φ) (Enveloping.resRegularUnderlying ψ)

theorem tensorRegular_action (φ : R →ₐ[k] S) (ψ : U →ₐ[k] V)
    (a : R ⊗[k] U) (z : OuterTensor.Obj k R U
      ((AlgebraInduction.res φ).obj (ModuleCat.of S S))
      ((AlgebraInduction.res ψ).obj (ModuleCat.of V V))) :
    tensorRegularUnderlying φ ψ (a • z)=
      Algebra.TensorProduct.map φ ψ a*tensorRegularUnderlying φ ψ z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb =>
    rw [add_smul,map_add,ha,hb,map_add,add_mul]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [smul_add,map_add,map_add,hx,hy,mul_add]
    | tmul x y =>
      change (φ a*(show S from x)) ⊗ₜ[k] (ψ b*(show V from y))=
        (φ a ⊗ₜ[k] ψ b)*((show S from x) ⊗ₜ[k] (show V from y))
      exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

def tensorRegularIso (φ : R →ₐ[k] S) (ψ : U →ₐ[k] V) :
    ((OuterTensor.bifunctor k R U).obj
      ((AlgebraInduction.res φ).obj (ModuleCat.of S S))).obj
      ((AlgebraInduction.res ψ).obj (ModuleCat.of V V)) ≅
    (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj
      (ModuleCat.of (S ⊗[k] V) (S ⊗[k] V)) := by
  let X := ((OuterTensor.bifunctor k R U).obj
      ((AlgebraInduction.res φ).obj (ModuleCat.of S S))).obj
      ((AlgebraInduction.res ψ).obj (ModuleCat.of V V))
  let Y := (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj
      (ModuleCat.of (S ⊗[k] V) (S ⊗[k] V))
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Y) (m₁ := X.isModule) (m₂ := Y.isModule)
    { __ := (tensorRegularUnderlying φ ψ).toAddEquiv
      map_smul' := tensorRegular_action φ ψ }

theorem resolution_pd {R : Type} [Ring R] {M : ModuleCat R}
    (P : CategoryTheory.ProjectiveResolution M) (d : ℕ)
    (hb : ∀ i, d < i → IsZero (P.complex.X i)) : HasProjectiveDimensionLE M d := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f,hf,rfl⟩ := P.extMk_surjective α (i+1) rfl
  have h := (hb i (by omega)).eq_of_src f 0
  subst f
  exact P.extMk_zero _ _

end Generic

abbrev leftT := (AlgebraInduction.res inclusionC).obj (ModuleCat.of T T)
abbrev rightT := (AlgebraInduction.res inclusionC.op).obj (ModuleCat.of Tᵐᵒᵖ Tᵐᵒᵖ)
abbrev leftProduct := ModuleCat.of A (A × Resolution.Dual)
abbrev rightProduct := ModuleCat.of Aᵐᵒᵖ (Aᵐᵒᵖ × Resolution.Dual)

def leftTEquiv : leftProduct ≃ₗ[A] leftT where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply TrivSqZeroExt.ext
    · rfl
    · change a • (show A × Resolution.Dual from x).2=
        a • (show A × Resolution.Dual from x).2+
          MulOpposite.op (show A × Resolution.Dual from x).1 • (0 : Resolution.Dual)
      rw [smul_zero,add_zero]

def rightTEquiv : rightProduct ≃ₗ[Aᵐᵒᵖ] rightT where
  toFun x := MulOpposite.op (x.1.unop,x.2)
  invFun x := (MulOpposite.op x.unop.fst,x.unop.snd)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply MulOpposite.unop_injective
    apply TrivSqZeroExt.ext
    · rfl
    · change a • (show Aᵐᵒᵖ × Resolution.Dual from x).2=
        (show Aᵐᵒᵖ × Resolution.Dual from x).1.unop • (0 : Resolution.Dual)+
          a • (show Aᵐᵒᵖ × Resolution.Dual from x).2
      rw [smul_zero,zero_add]

abbrev oppositeCRestriction := AlgebraInduction.res Resolution.oppositeIso.symm.toAlgHom
instance oppositeCRestriction_isEquivalence : oppositeCRestriction.IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars Resolution.oppositeIso.symm.toRingEquiv.toRingHom).IsEquivalence

def rightDC := ModuleCat.of Aᵐᵒᵖ Resolution.Dual

def rightDualIso : oppositeCRestriction.obj TensorDualResolution.DC ≅ rightDC :=
  LinearEquiv.toModuleIso (X₁ := oppositeCRestriction.obj TensorDualResolution.DC)
    (X₂ := rightDC) (m₁ := (oppositeCRestriction.obj TensorDualResolution.DC).isModule)
    (m₂ := rightDC.isModule)
    { toFun := Resolution.dualReverse
      invFun := Resolution.dualReverse
      left_inv φ := by
        apply Resolution.dual_ext
        intro x
        change (show Resolution.Dual from φ) (Resolution.reverse (Resolution.reverse x))=
          (show Resolution.Dual from φ) x
        rw [Resolution.reverse_reverse]
      right_inv φ := by
        apply Resolution.dual_ext
        intro x
        change (show Resolution.Dual from φ) (Resolution.reverse (Resolution.reverse x))=
          (show Resolution.Dual from φ) x
        rw [Resolution.reverse_reverse]
      map_add' _ _ := rfl
      map_smul' r φ := by
        apply Resolution.dual_ext
        intro x
        change (show Resolution.Dual from φ) (Resolution.reverse x*Resolution.reverse r.unop)=
          (show Resolution.Dual from φ) (Resolution.reverse (r.unop*x))
        rw [Resolution.reverse_mul] }

def rightDualResolution : CategoryTheory.ProjectiveResolution rightDC :=
  transportResolution
    (oppositeCRestriction.mapProjectiveResolution Resolution.leftDualProjectiveResolution)
    rightDualIso

theorem rightDual_above (n : ℕ) (hn : 2 < n) :
    IsZero (rightDualResolution.complex.X n) :=
  oppositeCRestriction.map_isZero (TensorDualResolution.leftDual_above n hn)

theorem leftDual_finiteQ (n : ℕ) :
    Module.Finite ℚ (Resolution.leftDualProjectiveResolution.complex.X n) := by
  let := TensorDualResolution.leftDual_finite n
  exact Module.Finite.trans A _

theorem rightDual_finiteQ (n : ℕ) : Module.Finite ℚ (rightDualResolution.complex.X n) := by
  let := leftDual_finiteQ n
  change Module.Finite ℚ (oppositeCRestriction.obj (Resolution.leftDualProjectiveResolution.complex.X n))
  infer_instance

def leftProductResolution : CategoryTheory.ProjectiveResolution leftProduct :=
  OAI.Tachikawa.ProjectiveResolution.prod
    (OAI.Tachikawa.ProjectiveResolution.simpleSelf (ModuleCat.of A A))
    Resolution.leftDualProjectiveResolution

def rightProductResolution : CategoryTheory.ProjectiveResolution rightProduct :=
  OAI.Tachikawa.ProjectiveResolution.prod
    (OAI.Tachikawa.ProjectiveResolution.simpleSelf (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
    rightDualResolution

def leftTResolution : CategoryTheory.ProjectiveResolution leftT :=
  transportResolution leftProductResolution leftTEquiv.toModuleIso

def rightTResolution : CategoryTheory.ProjectiveResolution rightT :=
  transportResolution rightProductResolution rightTEquiv.toModuleIso

theorem leftT_above (n : ℕ) (hn : 2 < n) : IsZero (leftTResolution.complex.X n) :=
  OAI.Tachikawa.ProjectiveResolution.prod_above _ _ 2 n
    (fun i hi => OAI.Tachikawa.ProjectiveResolution.simpleSelf_above _ i (by omega))
    TensorDualResolution.leftDual_above hn

theorem rightT_above (n : ℕ) (hn : 2 < n) : IsZero (rightTResolution.complex.X n) :=
  OAI.Tachikawa.ProjectiveResolution.prod_above _ _ 2 n
    (fun i hi => OAI.Tachikawa.ProjectiveResolution.simpleSelf_above _ i (by omega))
    rightDual_above hn

theorem leftT_finiteQ (n : ℕ) : Module.Finite ℚ (leftTResolution.complex.X n) := by
  let := OAI.Tachikawa.moduleCatFinite (k := ℚ) (R := A) A
  let : Projective (OAI.Tachikawa.moduleCatObj (R := A) A) :=
    inferInstanceAs (Projective (ModuleCat.of A A))
  exact OAI.Tachikawa.ProjectiveResolution.prod_finite _ _
    (OAI.Tachikawa.ProjectiveResolution.simpleSelf_finite (k := ℚ) (R := A)
      (OAI.Tachikawa.moduleCatObj (R := A) A))
    leftDual_finiteQ n

theorem rightT_finiteQ (n : ℕ) : Module.Finite ℚ (rightTResolution.complex.X n) := by
  let := OAI.Tachikawa.moduleCatFinite (k := ℚ) (R := Aᵐᵒᵖ) Aᵐᵒᵖ
  let : Projective (OAI.Tachikawa.moduleCatObj (R := Aᵐᵒᵖ) Aᵐᵒᵖ) :=
    inferInstanceAs (Projective (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
  exact OAI.Tachikawa.ProjectiveResolution.prod_finite _ _
    (OAI.Tachikawa.ProjectiveResolution.simpleSelf_finite (k := ℚ) (R := Aᵐᵒᵖ)
      (OAI.Tachikawa.moduleCatObj (R := Aᵐᵒᵖ) Aᵐᵒᵖ))
    rightDual_finiteQ n

theorem leftT_finite (n : ℕ) : Module.Finite A (leftTResolution.complex.X n) := by
  let := leftT_finiteQ n
  exact Module.Finite.of_restrictScalars_finite ℚ A _

theorem rightT_finite (n : ℕ) : Module.Finite Aᵐᵒᵖ (rightTResolution.complex.X n) := by
  let := rightT_finiteQ n
  exact Module.Finite.of_restrictScalars_finite ℚ Aᵐᵒᵖ _

abbrev leftE := (AlgebraInduction.res inclusionB).obj (ModuleCat.of E E)
def leftEResolution : CategoryTheory.ProjectiveResolution leftE :=
  transportResolution
    (TensorExt.resolution ℚ A A leftTResolution leftTResolution leftT_finite leftT_finite)
    (tensorRegularIso inclusionC inclusionC)

theorem leftE_above (n : ℕ) (hn : 4 < n) : IsZero (leftEResolution.complex.X n) :=
  total_isZero_above _ _ 2 2 leftT_above leftT_above n hn

theorem leftE_projectiveDimension : HasProjectiveDimensionLE leftE 4 :=
  resolution_pd leftEResolution 4 leftE_above

end
end TachikawaCharZero.RestrictionDimension
