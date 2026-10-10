import OAI.RingTheory.Tachikawa.CokerComparison
import OAI.RingTheory.Tachikawa.StableSyzygy

/-! Characteristic-independent excerpt at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable {M N L : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R M] [Module R N] [Module R L] [Module k N] [Module k L]
  [IsScalarTower k R N] [IsScalarTower k R L]

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))
variable {n : ℕ} (ε : (Fin n → R) →ₗ[R] M)

lemma syzygyPair_natural (b : L →ₗ[R] LinearMap.ker ε) (φ : N →ₗ[R] L)
    (f : M →ₗ[R] N) :
    t.syzygyPair ε (b.comp φ) f = t.syzygyPair ε b (φ.comp f) := by
  simp only [syzygyPair_apply]
  rw [← LinearMap.comp_assoc, t.freeHomDual_natural, LinearMap.comp_assoc]

include t in

theorem exists_nonzero_postcomposition
    (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    (b : L →ₗ[R] LinearMap.ker ε) (φ : N →ₗ[R] L)
    (hb : b.comp φ ∉ projectiveFactors (k := k)) :
    ∃ f : M →ₗ[R] N, φ.comp f ∉ projectiveFactors (k := k) := by
  have hp : t.syzygyPair ε (b.comp φ) ≠ 0 :=
    mt (t.syzygyPair_eq_zero_iff ε hε d hd (b.comp φ)).mp hb
  have hex : ∃ f, t.syzygyPair ε (b.comp φ) f ≠ 0 := by
    by_contra! hn
    exact hp (LinearMap.ext hn)
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, fun hh => hf ?_⟩
  rw [syzygyPair_natural]
  exact t.syzygyPair_vanish_left ε i hi b (φ.comp f) hh

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B]
  [Module R C] [Module R D] [Module k B] [Module k D]
  [IsScalarTower k R B] [IsScalarTower k R D]

lemma projectiveFactors_conjugate_iff (f : A →ₗ[R] B) (e : C ≃ₗ[R] A) (v : B ≃ₗ[R] D) :
    (v.toLinearMap.comp f).comp e.toLinearMap ∈ projectiveFactors (k := k) ↔
      f ∈ projectiveFactors (k := k) := by
  constructor
  · intro h
    have hh := projectiveFactors_postcomp (projectiveFactors_precomp h e.symm.toLinearMap)
      v.symm.toLinearMap
    have he : v.symm.toLinearMap.comp (((v.toLinearMap.comp f).comp e.toLinearMap).comp e.symm.toLinearMap) = f := by
      ext x; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
    rw [he] at hh
    exact hh
  · intro h
    exact projectiveFactors_precomp (projectiveFactors_postcomp h v.toLinearMap) e.toLinearMap

namespace SymmetrizingForm
variable [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))

include t in

theorem exists_syzygy_postcomposition (U M L : FiniteModule k R) (n : ℕ)
    (b : L.obj →ₗ[R] (U.positive (n+1)).obj) (phi : M.obj →ₗ[R] L.obj)
    (h : b.comp phi ∉ projectiveFactors (k := k)) :
    ∃ beta : (U.positive n).obj →ₗ[R] M.obj, phi.comp beta ∉ projectiveFactors (k := k) := by
  exact t.exists_nonzero_postcomposition (U.positive n).cover.map
    (U.positive n).cover.surjective ((U.positive n).embed t) ((U.positive n).embed_injective t)
    (U.positive (n+1)).cover.map (U.positive (n+1)).cover.surjective b phi h
end SymmetrizingForm
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))


lemma negative_succ_left (M : FiniteModule k R) (n : ℕ) :
    (M.cosyzygy t).negative t n = M.negative t (n+1) := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg (fun L : FiniteModule k R => L.cosyzygy t) h

theorem descend_nonzero_composition (M U S : FiniteModule k R) (n : ℕ)
    (beta : (U.positive (n+1)).obj →ₗ[R] M.obj)
    (phi : M.obj →ₗ[R] (S.positive (n+2)).obj)
    (hn : phi.comp beta ∉ projectiveFactors (k := k)) :
    ∃ (g : (U.positive n).obj →ₗ[R] (M.cosyzygy t).obj)
      (psi : (M.cosyzygy t).obj →ₗ[R] (S.positive (n+1)).obj),
      psi.comp g ∉ projectiveFactors (k := k) := by
  let : Module.Injective R R := t.injective
  let PU := ModuleCat.of R (Fin (U.positive n).cover.rank → R)
  let PM := ModuleCat.of R (Fin (Module.finrank k M) → R)
  let PS := ModuleCat.of R (Fin (S.positive (n+1)).cover.rank → R)
  obtain ⟨h,g,hu,hl⟩ := exists_exact_square_down (P := PU) (Q := PM)
    (U.positive n).syzygyInclusion (U.positive n).cover.map
    (U.positive n).syzygyInclusion_injective (U.positive n).syzygyInclusion_exact
    (U.positive n).cover.surjective (M.embed t) (M.cosyzygyProjection t)
    (M.cosyzygyProjection_exact t) beta
  obtain ⟨h',psi,hu',hl'⟩ := exists_exact_square_down (P := PM) (Q := PS)
    (M.embed t) (M.cosyzygyProjection t) (M.embed_injective t)
    (M.cosyzygyProjection_exact t) (M.cosyzygyProjection_surjective t)
    (S.positive (n+1)).syzygyInclusion (S.positive (n+1)).cover.map
    (S.positive (n+1)).syzygyInclusion_exact phi
  refine ⟨g,psi,?_⟩
  apply mt (exact_square_factors_iff (P := PU) (Q := PS)
    (U.positive n).syzygyInclusion (U.positive n).cover.map
    (U.positive n).syzygyInclusion_injective (U.positive n).syzygyInclusion_exact
    (U.positive n).cover.surjective
    (S.positive (n+1)).syzygyInclusion (S.positive (n+1)).cover.map
    (S.positive (n+1)).syzygyInclusion_injective (S.positive (n+1)).syzygyInclusion_exact
    (S.positive (n+1)).cover.surjective
    (phi.comp beta) (h'.comp h) (psi.comp g) ?_ ?_).mpr hn
  · erw [LinearMap.comp_assoc,hu,← LinearMap.comp_assoc,hu',LinearMap.comp_assoc]
  · rw [← LinearMap.comp_assoc,hl',LinearMap.comp_assoc,hl,← LinearMap.comp_assoc]

theorem descend_nonzero_composition_iterated (U S : FiniteModule k R) (n : ℕ)
    (M : FiniteModule k R) (beta : (U.positive n).obj →ₗ[R] M.obj)
    (phi : M.obj →ₗ[R] (S.positive (n+1)).obj)
    (hn : phi.comp beta ∉ projectiveFactors (k := k)) :
    ∃ (g : U.obj →ₗ[R] (M.negative t n).obj)
      (psi : (M.negative t n).obj →ₗ[R] (S.positive 1).obj),
      psi.comp g ∉ projectiveFactors (k := k) := by
  induction n generalizing M with
  | zero => exact ⟨beta,phi,hn⟩
  | succ n ih =>
    obtain ⟨g,psi,hg⟩ := descend_nonzero_composition t M U S n beta phi hn
    rw [← negative_succ_left t M n]
    exact ih (M.cosyzygy t) g psi hg
end Tachikawa.FiniteModule

end
end OAI
