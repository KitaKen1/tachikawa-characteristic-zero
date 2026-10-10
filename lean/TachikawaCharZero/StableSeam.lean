import TachikawaCharZero.StableEnd
import OAI.RingTheory.Tachikawa.CompleteStable

/-! The actual negative-one stable Hom space. Symmetric stable duality
identifies Hom(X,Omega X) with the dual of the actual stable End(X).
This establishes its dimension and nonzero classes; generator naturality
and twist weights are separate obligations. -/
namespace TachikawaCharZero.StableSeam
noncomputable section
open TensorProfile OAI.Tachikawa
open scoped ModuleCat.Algebra

def finiteX : FiniteModule ℚ E where
  obj := X₂
  finite := StableEnd.finiteE

abbrev negativeOne := StableHom (k := ℚ) (R := E) (M := X₂) (N := finiteX.syzygy.obj)

def negativeOneEquiv : negativeOne ≃ₗ[ℚ] ℚ := by
  let t : SymmetrizingForm (k := ℚ) (R := E) := Starting.E_form
  let e := stablePostEquiv (k := ℚ) (R := E) (M := X₂)
    (N := finiteX.syzygy.obj) (N' := LinearMap.ker finiteX.cover.map) (LinearEquiv.refl E _)
  exact e.trans ((t.stableDualEquiv (M := finiteX) (N := X₂) finiteX.cover.map finiteX.cover.surjective
    t.freeEmbedding t.freeEmbedding_injective finiteX.syzygy.cover.map
    finiteX.syzygy.cover.surjective).trans
    (StableEnd.equiv.dualMap.symm.trans (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ)))

theorem negativeOne_finrank : Module.finrank ℚ negativeOne=1 := by
  rw [negativeOneEquiv.finrank_eq]
  exact Module.finrank_self ℚ

def negativeOneClass : negativeOne := negativeOneEquiv.symm 1

theorem negativeOneClass_ne_zero : negativeOneClass≠0 := by
  intro h
  have hh := congrArg negativeOneEquiv h
  simp only [negativeOneClass, LinearEquiv.apply_symm_apply, map_zero] at hh
  exact one_ne_zero hh

end
end TachikawaCharZero.StableSeam
