import TachikawaCharZero.TwistedTrace
import Mathlib.RingTheory.TensorProduct.Basic

/-! The universal trace-zero identity on C tensor C. -/
namespace TachikawaCharZero

open OAI.ArExplicit
open scoped TensorProduct

variable {k : Type*} [CommRing k] (q : k)

instance coordinateFree : Module.Free k (C q) :=
  Module.Free.of_basis (coordinateBasis q)

abbrev B := C q ⊗[k] C q

def tensorSigma : B q →ₗ[k] B q :=
  TensorProduct.map (sigma q).toLinearMap (sigma q).toLinearMap

def tensorVertex : B q :=
  BaseAlgebra.basisVector q .f ⊗ₜ[k] BaseAlgebra.basisVector q .f

def tensorTwistedCornerMap (a : B q) : B q →ₗ[k] B q :=
  (LinearMap.mulRight k (tensorVertex q)).comp
    ((LinearMap.mulLeft k a).comp (tensorSigma q))

@[simp] theorem tensorTwistedCornerMap_apply (a x : B q) :
    tensorTwistedCornerMap q a x = a * tensorSigma q x * tensorVertex q := rfl

@[simp] theorem tensorTwistedCornerMap_add (a b : B q) :
    tensorTwistedCornerMap q (a + b) =
      tensorTwistedCornerMap q a + tensorTwistedCornerMap q b := by
  ext x
  simp [add_mul]

@[simp] theorem tensorTwistedCornerMap_zero :
    tensorTwistedCornerMap q (0 : B q) = 0 := by
  ext x
  simp

theorem tensorTwistedCornerMap_tmul (a b : C q) :
    tensorTwistedCornerMap q (a ⊗ₜ[k] b) =
      TensorProduct.map (twistedCornerMap q a) (twistedCornerMap q b) := by
  ext x y
  simp [tensorSigma, tensorVertex, Algebra.TensorProduct.tmul_mul_tmul]

theorem tensorTwistedCorner_trace (a : B q) :
    LinearMap.trace k (B q) (tensorTwistedCornerMap q a) = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    rw [tensorTwistedCornerMap_tmul, LinearMap.trace_tensorProduct']
    simp [twistedCorner_trace]
  | add a b ha hb =>
    rw [tensorTwistedCornerMap_add, map_add, ha, hb, add_zero]

end TachikawaCharZero
