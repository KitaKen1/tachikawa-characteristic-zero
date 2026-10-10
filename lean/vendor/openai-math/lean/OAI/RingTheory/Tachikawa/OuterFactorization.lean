import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic

/-! Characteristic-independent excerpt from OpenAI Math Corner.lean,
fixed commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R]

omit [FiniteDimensional k R] in
lemma end_expansion {ι : Type*} [Fintype ι] (e : Module.Basis ι k R)
    (F : R →ₗ[k] R) :
    F = ∑ i, (e.coord i).smulRight (F (e i)) := by
  classical
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have h := congrArg F (e.sum_repr x)
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using h.symm

lemma outer_to_dual_formula
    (β : (R →ₗ[k] R) →ₗ[k] Module.Dual k R)
    (hleft : ∀ (a : R) (F : R →ₗ[k] R),
      β (F.comp (LinearMap.mulRight k a)) = (β F).comp (LinearMap.mulRight k a))
    (hright : ∀ (a : R) (F : R →ₗ[k] R),
      β ((LinearMap.mulRight k a).comp F) = (β F).comp (LinearMap.mulLeft k a)) :
    ∃ b : R, ∀ (φ : Module.Dual k R) (c p : R),
      β (φ.smulRight c) p = φ (b * c * p) := by
  let t : Module.Dual k R →ₗ[k] (R →ₗ[k] R) := LinearMap.smulRightₗ.flip 1
  let η : Module.Dual k R →ₗ[k] Module.Dual k R := β.comp t
  let b : R := (Module.evalEquiv k R).symm ((LinearMap.applyₗ (1 : R)).comp η)
  have hb (φ : Module.Dual k R) : φ b = β (φ.smulRight 1) 1 := by
    exact Module.apply_evalEquiv_symm_apply k R φ _
  have ht (φ : Module.Dual k R) (p : R) : β (φ.smulRight 1) p = φ (b * p) := by
    have h := congrArg (fun g : Module.Dual k R => g 1) (hleft p (φ.smulRight 1))
    have he : (φ.smulRight (1 : R)).comp (LinearMap.mulRight k p) =
        (φ.comp (LinearMap.mulRight k p)).smulRight 1 := by
      ext x
      rfl
    rw [he] at h
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, one_mul] at h
    rw [← hb] at h
    exact h.symm
  refine ⟨b, ?_⟩
  intro φ c p
  have he : (LinearMap.mulRight k c).comp (φ.smulRight (1 : R)) = φ.smulRight c := by
    ext x
    simp
  have h := congrArg (fun g : Module.Dual k R => g p) (hright c (φ.smulRight 1))
  rw [he] at h
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
  rw [h, ht, mul_assoc]

omit [FiniteDimensional k R] in

lemma outer_central_is_mulLeft (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k a) = (LinearMap.mulRight k a).comp F) :
    F = LinearMap.mulLeft k (F 1) := by
  ext x
  have h := congrArg (fun g : R →ₗ[k] R => g 1) (hF x)
  simpa using h

lemma outer_factorization_trace
    (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k a) = (LinearMap.mulRight k a).comp F)
    (β : (R →ₗ[k] R) →ₗ[k] Module.Dual k R)
    (hleft : ∀ (a : R) (G : R →ₗ[k] R),
      β (G.comp (LinearMap.mulRight k a)) = (β G).comp (LinearMap.mulRight k a))
    (hright : ∀ (a : R) (G : R →ₗ[k] R),
      β ((LinearMap.mulRight k a).comp G) = (β G).comp (LinearMap.mulLeft k a)) :
    ∃ d : R, ∀ p : R, β F p =
      LinearMap.trace k R ((LinearMap.mulLeft k d).comp (LinearMap.mulRight k p)) := by
  classical
  obtain ⟨b, hb⟩ := outer_to_dual_formula β hleft hright
  refine ⟨b * F 1, ?_⟩
  intro p
  let e := Module.finBasis k R
  conv_lhs => rw [end_expansion e F]
  simp only [map_sum, LinearMap.sum_apply, hb]
  rw [LinearMap.trace_eq_matrix_trace k e]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  have hFi : F (e i) = F 1 * e i := by
    rw [outer_central_is_mulLeft F hF]
    simp
  simp only [Module.Basis.coord_apply, hFi, mul_assoc]

end Tachikawa

end
end OAI
