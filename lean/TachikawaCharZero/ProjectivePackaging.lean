import TachikawaCharZero.Initial
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! The generic exact-sequence packaging is adapted from OpenAI Math,
`OAI/RingTheory/Tachikawa/StableDuality.lean`, `resolutionOfExact`, at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The characteristic-zero differentials below are new. -/
namespace TachikawaCharZero
noncomputable section
open CategoryTheory CategoryTheory.Limits

def resolutionOfExact {R : Type*} [Ring R] (M : ModuleCat R) (P : ℕ → ModuleCat R)
    (d : ∀ n, P (n+1) ⟶ P n) (ε : P 0 ⟶ M)
    (hd : ∀ n, Function.Exact (d (n+1)) (d n))
    (hε : Function.Exact (d 0) ε) (surj : Function.Surjective ε)
    (proj : ∀ n, Projective (P n)) : ProjectiveResolution M := by
  let sq : ∀ n, d (n+1) ≫ d n = 0 := fun n => ModuleCat.hom_ext <| LinearMap.ext <|
    (hd n).apply_apply_eq_zero
  let K := ChainComplex.of P d sq
  let π : K ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact hε.apply_apply_eq_zero⟩
  refine {complex := K, π := π, projective := proj, quasiIso := ⟨fun n => ?_⟩}
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _
      (by rfl) (by simp; rfl) (by rfl)]
    · constructor
      · apply (ShortComplex.moduleCat_exact_iff _).2
        change ∀ x : P 0, ε x = 0 → ∃ y : P 1, K.d 1 0 y = x
        have hk : K.d 1 0 = d 0 := ChainComplex.of_d P d 0
        rw [hk]
        exact fun x => (hε x).mp
      · change Epi ε
        exact (ModuleCat.epi_iff_surjective ε).2 surj
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
      apply (ShortComplex.moduleCat_exact_iff _).2
      change ∀ x : P (n+1), K.d (n+1) n x = 0 → ∃ y, K.d (n+2) (n+1) y = x
      have hk₁ : K.d (n+1) n = d n := ChainComplex.of_d _ _ _
      have hk₂ : K.d (n+2) (n+1) = d (n+1) := ChainComplex.of_d _ _ _
      rw [hk₁, hk₂]
      exact fun x => (hd n x).mp
    · exact ChainComplex.exactAt_succ_single_obj _ _

namespace Resolution

def resObj : ℕ → ModuleCat A
  | 0 => ModuleCat.of A Cf
  | _+1 => ModuleCat.of A Ce

def resD : ∀ n, resObj (n+1) ⟶ resObj n
  | 0 => ModuleCat.ofHom initialMap
  | n+1 => ModuleCat.ofHom (ceDiff ((-2:ℚ)^n))

theorem resD_exact (n : ℕ) : Function.Exact (resD (n+1)) (resD n) := by
  cases n with
  | zero =>
    change Function.Exact (ceDiff 1) initialMap
    exact initial_exact
  | succ n => exact ceDiff_exact_all_degrees n

def projectiveResolution : ProjectiveResolution (ModuleCat.of A Simple) :=
  resolutionOfExact _ resObj resD (ModuleCat.ofHom augmentation)
    resD_exact augmentation_exact augmentation_surjective
    (fun n => by cases n <;> dsimp [resObj] <;> infer_instance)

theorem projectiveResolution_d (n : ℕ) :
    projectiveResolution.complex.d (n+1) n = resD n := by
  exact ChainComplex.of_d _ _ n

end Resolution
end
end TachikawaCharZero
