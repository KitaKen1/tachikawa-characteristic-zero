import TachikawaCharZero.TriangularWitness
import TachikawaCharZero.TriangularHomotopy

/-! The actual triangular cone cokernel and its induced module are
nonprojective. A supposed projective cokernel contracts the cone; its
unshifted diagonal contracts the original complete resolution of X. -/
namespace TachikawaCharZero.TriangularNonprojective
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory OAI.Tachikawa
open scoped ModuleCat.Algebra

section Generic
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
include k

theorem contraction_of_projective_coker (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (hP : TotallyAcyclic P) (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    (hp : Module.Projective R (CokerAt P 0)) : Nonempty (Homotopy (𝟙 P) 0) := by
  let := FinalTransfer.coker_finite P fin
  have hf : CokerAt.map (𝟙 P) 0 ∈ projectiveFactors (k:=k) := by
    rw [CokerAt.map_id]
    exact id_mem_projectiveFactors_iff.mpr hp
  exact nullhomotopic_of_coker_factors (𝟙 P) hP hP.1 proj fin proj hf

theorem projective_coker_of_contraction (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j)) (h : Homotopy (𝟙 P) 0) :
    Module.Projective R (CokerAt P 0) := by
  let := FinalTransfer.coker_finite P fin
  have hf := coker_factors_of_nullhomotopic (k:=k) (𝟙 P) h (fin (-1)) (proj (-1))
  rw [CokerAt.map_id] at hf
  exact id_mem_projectiveFactors_iff.mp hf

end Generic
open TriangularWitness

theorem Z_nonprojective : ¬ Module.Projective Lambda Z := by
  intro hp
  obtain ⟨h⟩ := contraction_of_projective_coker (k:=ℚ) cone cone_totallyAcyclic
    cone_finite cone_projective hp
  let hP := TriangularHomotopy.contraction F lift h
  let := projective_coker_of_contraction (k:=ℚ) TateProfile.P
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form) hP
  apply TensorProfile.not_projective
  exact Module.Projective.of_equiv (StableSeam.finiteX.cokerEquiv TateProfile.form)

theorem M_nonprojective : ¬ Module.Projective Gamma M :=
  FinalTransfer.M_nonprojective cone cone_finite Z_nonprojective

/-- The sole remaining mathematical acceptance gate for the actual witness. -/
theorem target_of_selfHom_vanishing
    (van : ∀ a : ℤ, 0<a ∨ a≤ -2 →
      Subsingleton (VectorSplit.H (completeHom (k:=ℚ) cone (ModuleCat.of Lambda Z)) a)) :
    Target := TriangularWitness.target_of_remaining Z_nonprojective van

end
end TachikawaCharZero.TriangularNonprojective
