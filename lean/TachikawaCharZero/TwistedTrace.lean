import TachikawaCharZero.SignedAutomorphism
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! The signed trace obstruction at the algebraic level. These are actual
LinearMap traces, connected to the coordinate matrices by a transported basis. -/
namespace TachikawaCharZero

open OAI.ArExplicit OAI.ArExplicit.Letter
open scoped TensorProduct

variable {k : Type*} [CommRing k] (q : k)

noncomputable def coordinateBasis : Module.Basis Letter k (C q) :=
  (Pi.basisFun k Letter).map (BaseAlgebra.coordinateLinearEquiv q).symm

@[simp] theorem coordinateBasis_apply (i : Letter) :
    coordinateBasis q i = BaseAlgebra.basisVector q i := by
  ext l
  simp [coordinateBasis, BaseAlgebra.coordinateLinearEquiv,
    BaseAlgebra.coordinateAddEquiv, BaseAlgebra.coordinates,
    BaseAlgebra.basisVector, Pi.single_apply, eq_comm]
  change (if i = l then (1 : k) else 0) = (Pi.single i (1 : k) : Letter → k) l
  simp [Pi.single_apply, eq_comm]

@[simp] theorem coordinateBasis_repr (a : C q) (i : Letter) :
    (coordinateBasis q).repr a i = a.coeff i := by
  simp [coordinateBasis, BaseAlgebra.coordinateLinearEquiv,
    BaseAlgebra.coordinateAddEquiv, BaseAlgebra.coordinates]
  rfl

def twistedCornerMap (a : C q) : C q →ₗ[k] C q :=
  (LinearMap.mulRight k (BaseAlgebra.basisVector q .f)).comp
    ((LinearMap.mulLeft k a).comp (sigma q).toLinearMap)

@[simp] theorem twistedCornerMap_apply (a x : C q) :
    twistedCornerMap q a x = a * signed q x * BaseAlgebra.basisVector q .f := rfl

def twistedCornerMatrix (a : C q) : Matrix Letter Letter k :=
  fun i col => (twistedCornerMap q a (BaseAlgebra.basisVector q col)).coeff i

theorem twistedCornerMatrix_trace (a : C q) :
    Matrix.trace (twistedCornerMatrix q a) = 0 := by
  change (∑ i : Letter, twistedCornerMatrix q a i i) = 0
  change (∑ i ∈ ({.e, .x, .y, .z, .u, .v, .t, .j, .f, .n} : Finset Letter),
    twistedCornerMatrix q a i i) = 0
  simp [twistedCornerMatrix, BaseAlgebra.product, signCoeff]

theorem twistedCorner_trace (a : C q) :
    LinearMap.trace k (C q) (twistedCornerMap q a) = 0 := by
  rw [LinearMap.trace_eq_matrix_trace k (coordinateBasis q)]
  have h : LinearMap.toMatrix (coordinateBasis q) (coordinateBasis q)
      (twistedCornerMap q a) = twistedCornerMatrix q a := by
    ext i col
    simp [LinearMap.toMatrix_apply, twistedCornerMatrix]
  rw [h, twistedCornerMatrix_trace]

end TachikawaCharZero
