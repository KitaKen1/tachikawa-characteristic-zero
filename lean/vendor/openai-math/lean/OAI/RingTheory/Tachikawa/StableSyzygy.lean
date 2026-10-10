import OAI.RingTheory.Tachikawa.TwistHom

/-! Characteristic-free syzygy/cosyzygy maps, extracted unchanged from
OpenAI Math StableLift.lean lines 367-389, fixed commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Only imports and surrounding namespace/section wrappers differ. -/
namespace OAI
noncomputable section

namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))

def syzygyInclusion (M : FiniteModule k R) : M.syzygy.obj →ₗ[R] (Fin M.cover.rank → R) :=
  (LinearMap.ker M.cover.map).subtype
lemma syzygyInclusion_injective (M : FiniteModule k R) : Function.Injective M.syzygyInclusion :=
  Subtype.val_injective
lemma syzygyInclusion_exact (M : FiniteModule k R) : Function.Exact M.syzygyInclusion M.cover.map := by
  intro x
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩

def cosyzygyProjection (M : FiniteModule k R) :
    (Fin (Module.finrank k M) → R) →ₗ[R] (M.cosyzygy t).obj :=
  (LinearMap.range (M.embed t)).mkQ
lemma cosyzygyProjection_surjective (M : FiniteModule k R) : Function.Surjective (M.cosyzygyProjection t) :=
  Submodule.mkQ_surjective _
lemma cosyzygyProjection_exact (M : FiniteModule k R) :
    Function.Exact (M.embed t) (M.cosyzygyProjection t) := by
  intro x
  exact Submodule.Quotient.mk_eq_zero _

end Tachikawa.FiniteModule
end
end OAI
