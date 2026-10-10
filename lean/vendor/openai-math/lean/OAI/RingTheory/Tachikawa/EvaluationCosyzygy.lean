import OAI.RingTheory.Tachikawa.StableEvaluation
import OAI.RingTheory.Tachikawa.CompleteStable

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) [FiniteDimensional k X]
  (M : FiniteModule k (Alg k S R)) [Module.Projective Rᵐᵒᵖ (Obj M.obj)]
  (P : ChainComplex (ModuleCat.{0} S) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite S (P.X j)) (proj : ∀ j, Module.Projective S (P.X j))

omit [Module.Projective Rᵐᵒᵖ (Obj M.obj)] in
lemma evalFree_finite (Q : ModuleCat.{0} (Alg k S R)) [Module.Finite (Alg k S R) Q] :
    Module.Finite S (evalObj (k := k) X Q) := by
  let : FiniteDimensional k Q := Module.Finite.trans (Alg k S R) Q
  infer_instance

def evalCosyCokerStableEquiv (j : ℤ)
    (e : StableEquiv (k := k) (evalObj (k := k) X M.obj) (ModuleCat.of S (CokerAt P j))) :
    StableEquiv (k := k) (evalObj (k := k) X (M.cosyzygy (envelopingForm u t)).obj)
      (ModuleCat.of S (CokerAt P (j-1))) := by
  let τ := envelopingForm u t
  let J := ModuleCat.of (Alg k S R) (Fin (Module.finrank k M) → Alg k S R)
  let : Module.Finite (Alg k S R) J := inferInstanceAs (Module.Finite (Alg k S R) (Fin (Module.finrank k M) → Alg k S R))
  let : Module.Projective (Alg k S R) J := inferInstanceAs (Module.Projective (Alg k S R) (Fin (Module.finrank k M) → Alg k S R))
  let : Module.Finite S (evalObj (k := k) X J) := evalFree_finite (k := k) X J
  let : Module.Projective S (evalObj (k := k) X J) := by infer_instance
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let p : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  have hi : Function.Injective i := M.embed_injective τ
  have he : Function.Exact i p := fun _ => Submodule.Quotient.mk_eq_zero _
  have hs : Function.Surjective p := Submodule.mkQ_surjective _
  let : Module.Injective S S := u.injective
  let := fin (j-1)
  let := proj (j-1)
  exact StableEquiv.down (P := evalObj (k := k) X J) (Q := P.X (j-1))
    (evalMap (k := k) X i).hom (evalMap (k := k) X p).hom
    (evalMap_injective X t i hi) (evalMap_exact X t i p hi he hs) (evalMap_surjective X p hs)
    (CokerAt.δ P j (j-1)) (CokerAt.π P (j-1))
    (CokerAt.δ_injective P hP j (j-1) (by omega))
    (CokerAt.δ_π_exact P j (j-1) (by omega)) (CokerAt.π_surjective P (j-1)) e

end Tachikawa.Enveloping

end
end OAI
