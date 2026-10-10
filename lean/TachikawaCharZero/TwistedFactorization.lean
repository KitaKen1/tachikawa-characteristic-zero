import TachikawaCharZero.TensorTrace
import TachikawaCharZero.Simple
import OAI.RingTheory.Tachikawa.OuterFactorization

/-! The characteristic-zero algebraic part of the twisted obstruction.
The trace formula retains the inverse automorphism. Its rational
specialization excludes every finite sum of ordinary outer factorizations
with the stated bimodule compatibility. Reduction from a bounded derived
factorization to these ordinary maps remains a separate obligation. -/
namespace TachikawaCharZero.TwistedFactorization
noncomputable section
open OAI.Tachikawa
open scoped TensorProduct

section Generic
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R]

omit [FiniteDimensional k R] in
theorem twisted_central_is_mulLeft (θ : R ≃ₐ[k] R) (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k (θ a)) =
      (LinearMap.mulRight k a).comp F) :
    F=(LinearMap.mulLeft k (F 1)).comp θ.symm.toLinearMap := by
  ext x
  have h := congrArg (fun g : R →ₗ[k] R => g 1) (hF (θ.symm x))
  simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply, one_mul,
    AlgEquiv.apply_symm_apply, LinearMap.mulLeft_apply,
    AlgEquiv.toLinearMap_apply] using h

theorem twisted_factorization_trace (θ : R ≃ₐ[k] R) (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k (θ a)) =
      (LinearMap.mulRight k a).comp F)
    (β : (R →ₗ[k] R) →ₗ[k] Module.Dual k R)
    (hleft : ∀ (a : R) (G : R →ₗ[k] R),
      β (G.comp (LinearMap.mulRight k a)) = (β G).comp (LinearMap.mulRight k a))
    (hright : ∀ (a : R) (G : R →ₗ[k] R),
      β ((LinearMap.mulRight k a).comp G) = (β G).comp (LinearMap.mulLeft k a)) :
    ∃ d : R, ∀ p : R, β F p = LinearMap.trace k R
      ((LinearMap.mulRight k p).comp ((LinearMap.mulLeft k d).comp θ.symm.toLinearMap)) := by
  classical
  obtain ⟨b,hb⟩ := outer_to_dual_formula β hleft hright
  refine ⟨b*F 1,?_⟩
  intro p
  let e := Module.finBasis k R
  conv_lhs => rw [end_expansion e F]
  simp only [map_sum, LinearMap.sum_apply, hb]
  rw [LinearMap.trace_eq_matrix_trace k e]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, AlgEquiv.toLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hFi : F (e i)=F 1*θ.symm (e i) := by
    exact LinearMap.congr_fun (twisted_central_is_mulLeft θ F hF) (e i)
  simp only [Module.Basis.coord_apply, hFi, mul_assoc]

end Generic

abbrev B₀ := B (2 : ℚ)
def theta : B₀ ≃ₐ[ℚ] B₀ := Algebra.TensorProduct.congr (sigma 2) (sigma 2)
def character : B₀ →ₐ[ℚ] ℚ :=
  Algebra.TensorProduct.productMap Resolution.character Resolution.character
def eta : B₀ →ₗ[ℚ] Module.Dual ℚ B₀ :=
  character.toLinearMap.smulRight character.toLinearMap

theorem theta_symm_linear : theta.symm.toLinearMap=tensorSigma (2 : ℚ) := by
  ext x y
  rfl

theorem character_theta (x : B₀) : character (theta x)=character x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    change ((1 : ℚ)*x.coeff .f)*((1 : ℚ)*y.coeff .f)=x.coeff .f*y.coeff .f
    simp only [one_mul]

theorem eta_left (a b : B₀) : eta (a*b)=(eta b).comp (LinearMap.mulRight ℚ a) := by
  apply LinearMap.ext
  intro x
  change (character (a*b))*character x = character b*character (x*a)
  rw [map_mul,map_mul]
  ring

theorem eta_twisted_right (a b : B₀) :
    eta (a*theta b)=(eta a).comp (LinearMap.mulLeft ℚ b) := by
  apply LinearMap.ext
  intro x
  change (character (a*theta b))*character x = character a*character (b*x)
  rw [map_mul,character_theta,map_mul,mul_assoc]

theorem eta_one_vertex : eta 1 (tensorVertex (2 : ℚ))=1 := by
  change character 1 * character (tensorVertex (2 : ℚ))=1
  rw [map_one]
  change (1 : ℚ)*(1*1)=1
  norm_num

theorem ordinary_factorization_vertex_zero
    (α : B₀ →ₗ[ℚ] (B₀ →ₗ[ℚ] B₀))
    (hαleft : ∀ a b : B₀, α (a*b)=(α b).comp (LinearMap.mulRight ℚ a))
    (hαright : ∀ a b : B₀, α (a*theta b)=(LinearMap.mulRight ℚ b).comp (α a))
    (β : (B₀ →ₗ[ℚ] B₀) →ₗ[ℚ] Module.Dual ℚ B₀)
    (hβleft : ∀ a F, β (F.comp (LinearMap.mulRight ℚ a)) =
      (β F).comp (LinearMap.mulRight ℚ a))
    (hβright : ∀ a F, β ((LinearMap.mulRight ℚ a).comp F) =
      (β F).comp (LinearMap.mulLeft ℚ a)) :
    β (α 1) (tensorVertex (2 : ℚ))=0 := by
  have hα : ∀ a : B₀, (α 1).comp (LinearMap.mulRight ℚ (theta a)) =
      (LinearMap.mulRight ℚ a).comp (α 1) := by
    intro a
    rw [← hαleft,← hαright,mul_one,one_mul]
  obtain ⟨d,hd⟩ := twisted_factorization_trace theta (α 1) hα β hβleft hβright
  rw [hd,theta_symm_linear]
  exact tensorTwistedCorner_trace 2 d

theorem eta_not_finite_sum {ι : Type*} [Fintype ι]
    (α : ι → B₀ →ₗ[ℚ] (B₀ →ₗ[ℚ] B₀))
    (hαleft : ∀ i a b, α i (a*b)=(α i b).comp (LinearMap.mulRight ℚ a))
    (hαright : ∀ i a b, α i (a*theta b)=(LinearMap.mulRight ℚ b).comp (α i a))
    (β : ι → (B₀ →ₗ[ℚ] B₀) →ₗ[ℚ] Module.Dual ℚ B₀)
    (hβleft : ∀ i a F, β i (F.comp (LinearMap.mulRight ℚ a)) =
      (β i F).comp (LinearMap.mulRight ℚ a))
    (hβright : ∀ i a F, β i ((LinearMap.mulRight ℚ a).comp F) =
      (β i F).comp (LinearMap.mulLeft ℚ a)) :
    (∑ i, (β i).comp (α i))≠eta := by
  classical
  intro h
  have he := congrArg (fun f : B₀ →ₗ[ℚ] Module.Dual ℚ B₀ =>
    f 1 (tensorVertex (2 : ℚ))) h
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,eta_one_vertex] at he
  have hz : (∑ i, β i (α i 1) (tensorVertex (2 : ℚ)))=0 :=
    Finset.sum_eq_zero (fun i _ => ordinary_factorization_vertex_zero
      (α i) (hαleft i) (hαright i) (β i) (hβleft i) (hβright i))
  exact zero_ne_one (hz.symm.trans he)

end
end TachikawaCharZero.TwistedFactorization
