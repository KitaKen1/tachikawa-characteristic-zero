import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! Scalar endomorphisms pass through the fully faithful single functor.
For a one-dimensional module over the ground field, this allows comparison
of isomorphism transports without computing either isomorphism. -/
namespace TachikawaCharZero.SingleScalarEnd
noncomputable section
open CategoryTheory

theorem through_full (k : Type*) [Ring k]
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear k C] [Linear k D] (F : C ⥤ D) [F.Full] [F.Linear k]
    (X : C) (h : ∀ f : X ⟶ X, ∃ r : k, f=r • 𝟙 X)
    (g : F.obj X ⟶ F.obj X) : ∃ r : k, g=r • 𝟙 (F.obj X) := by
  obtain ⟨r,hr⟩ := h (F.preimage g)
  refine ⟨r, ?_⟩
  rw [← F.map_preimage g, hr]
  simp

theorem single (k : Type*) [Ring k]
    {C : Type*} [Category* C] [Abelian C] [Linear k C] [HasDerivedCategory C]
    (X : C) (h : ∀ f : X ⟶ X, ∃ r : k, f=r • 𝟙 X) (n : ℤ)
    (g : (DerivedCategory.singleFunctor C n).obj X ⟶
      (DerivedCategory.singleFunctor C n).obj X) :
    ∃ r : k, g=r • 𝟙 ((DerivedCategory.singleFunctor C n).obj X) :=
  through_full k (DerivedCategory.singleFunctor C n) X h g

open scoped ModuleCat.Algebra
theorem module_one (k A : Type*) [Field k] [Ring A] [Algebra k A]
    (M : ModuleCat A) (h : Module.finrank k M=1) (f : M ⟶ M) :
    ∃ r : k, f=r • 𝟙 M := by
  obtain ⟨r,hr,_⟩ :=
    (f.hom.restrictScalars k).existsUnique_eq_smul_id_of_finrank_eq_one h
  refine ⟨r, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun hr x

end
end TachikawaCharZero.SingleScalarEnd
