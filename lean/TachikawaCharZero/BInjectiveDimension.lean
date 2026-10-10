import TachikawaCharZero.TensorDualResolution
import OAI.RingTheory.Tachikawa.FiniteDual
import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-! The actual rational DB has a bounded right projective resolution, and
the regular left B-module has injective dimension at most four. We move
the left resolution through the opposite-algebra equivalence, rather than
repeating the signed corner calculation. The generic dualization API is
extracted from OpenAI Math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0). This is an input to, not the proof of, the derived-to-ordinary
twisted factorization reduction. -/
namespace TachikawaCharZero.BInjectiveDimension
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open TensorDualResolution

def oppositeB : B₀ ≃ₐ[ℚ] B₀ᵐᵒᵖ :=
  (Algebra.TensorProduct.congr Resolution.oppositeIso Resolution.oppositeIso).trans
    (Algebra.TensorProduct.opAlgEquiv ℚ ℚ Resolution.A Resolution.A)

def rightDB : ModuleCat B₀ᵐᵒᵖ := ModuleCat.of B₀ᵐᵒᵖ (DualBimodule ℚ B₀)
abbrev oppositeRestriction := ModuleCat.restrictScalars oppositeB.symm.toRingHom

instance oppositeRestriction_isEquivalence : oppositeRestriction.IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars oppositeB.symm.toRingEquiv.toRingHom).IsEquivalence

def antiLinear : B₀ →ₗ[ℚ] B₀ := oppositeB.symm.toLinearMap.comp
  (MulOpposite.opLinearEquiv ℚ).toLinearMap

def inverseAntiLinear : B₀ →ₗ[ℚ] B₀ :=
  (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap.comp oppositeB.toLinearMap

def oppositeDualIso : oppositeRestriction.obj DB ≅ rightDB :=
  LinearEquiv.toModuleIso (X₁ := oppositeRestriction.obj DB) (X₂ := rightDB)
    (m₁ := (oppositeRestriction.obj DB).isModule) (m₂ := rightDB.isModule)
    { toFun := fun φ => (show Module.Dual ℚ B₀ from φ).comp antiLinear
      invFun := fun ψ => (show Module.Dual ℚ B₀ from ψ).comp inverseAntiLinear
      left_inv φ := by
        apply LinearMap.ext
        intro x
        change (show Module.Dual ℚ B₀ from φ) (oppositeB.symm (oppositeB x))=
          (show Module.Dual ℚ B₀ from φ) x
        rw [AlgEquiv.symm_apply_apply]
      right_inv ψ := by
        apply LinearMap.ext
        intro x
        change (show Module.Dual ℚ B₀ from ψ)
          ((oppositeB (oppositeB.symm (MulOpposite.op x))).unop)=
            (show Module.Dual ℚ B₀ from ψ) x
        rw [AlgEquiv.apply_symm_apply]
        rfl
      map_add' _ _ := rfl
      map_smul' r φ := by
        apply LinearMap.ext
        intro x
        change (show Module.Dual ℚ B₀ from φ)
          (oppositeB.symm (MulOpposite.op x)*oppositeB.symm r)=
            (show Module.Dual ℚ B₀ from φ) (oppositeB.symm (MulOpposite.op (r.unop*x)))
        exact congrArg (show Module.Dual ℚ B₀ from φ)
          (map_mul oppositeB.symm (MulOpposite.op x) r).symm }

def rightResolution : ProjectiveResolution rightDB :=
  transportResolution (oppositeRestriction.mapProjectiveResolution leftResolution) oppositeDualIso

theorem rightResolution_above (n : ℕ) (hn : 4 < n) :
    IsZero (rightResolution.complex.X n) :=
  oppositeRestriction.map_isZero (leftResolution_above n hn)

theorem right_projectiveDimension : HasProjectiveDimensionLE rightDB 4 := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f,hf,rfl⟩ := rightResolution.extMk_surjective α (i+1) rfl
  have h := (rightResolution_above i (by omega)).eq_of_src f 0
  subst f
  exact rightResolution.extMk_zero _ _

def rightUnderlying : rightDB ≃ₗ[ℚ] Module.Dual ℚ B₀ where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c φ := by
    change (algebraMap ℚ B₀ᵐᵒᵖ c) • (show DualBimodule ℚ B₀ from φ)=
      c • (show DualBimodule ℚ B₀ from φ)
    exact IsScalarTower.algebraMap_smul B₀ᵐᵒᵖ c (show DualBimodule ℚ B₀ from φ)

def doubleDualRegularEquiv : B₀ ≃ₗ[B₀] LeftDual (k := ℚ) rightDB where
  __ := ((Module.evalEquiv ℚ B₀).trans rightUnderlying.dualMap).toAddEquiv
  map_smul' r x := by
    apply LeftDual.ext
    intro φ
    change (show DualBimodule ℚ B₀ from φ) (r*x)=
      (show DualBimodule ℚ B₀ from (MulOpposite.op r) • φ) x
    rfl

def regular : ModuleCat B₀ := ModuleCat.of B₀ B₀
def doubleDualRegularIso : regular ≅ leftDualObj (k := ℚ) rightDB :=
  doubleDualRegularEquiv.toModuleIso

theorem regular_ext_zero (V : ModuleCat B₀) (n : ℕ) (hn : 4 < n) :
    Subsingleton (CategoryTheory.Abelian.Ext V regular n) := by
  let : Subsingleton (CategoryTheory.Abelian.Ext V (leftDualObj (k := ℚ) rightDB) n) :=
    dualResolution_ext_zero rightResolution 4 rightResolution_above V n hn
  exact (extIso (k := ℚ) (Iso.refl V) doubleDualRegularIso n).injective.subsingleton

theorem regular_injectiveDimension : HasInjectiveDimensionLE regular 4 := by
  apply HasInjectiveDimensionLT.mk
  intro n hn V e
  let : Subsingleton (CategoryTheory.Abelian.Ext V regular n) :=
    regular_ext_zero V n (by omega)
  exact Subsingleton.elim _ _

def regularCoresolution : InjectiveResolution regular where
  cocomplex := (dualResolution (k := ℚ) rightResolution).cocomplex
  injective n := (dualResolution (k := ℚ) rightResolution).injective n
  ι := (CochainComplex.single₀ (ModuleCat B₀)).map doubleDualRegularIso.hom ≫
    (dualResolution (k := ℚ) rightResolution).ι
  quasiIso := inferInstance

theorem regularCoresolution_above (n : ℕ) (hn : 4 < n) :
    IsZero (regularCoresolution.cocomplex.X n) :=
  dualResolution_above rightResolution 4 rightResolution_above n hn

end
end TachikawaCharZero.BInjectiveDimension
