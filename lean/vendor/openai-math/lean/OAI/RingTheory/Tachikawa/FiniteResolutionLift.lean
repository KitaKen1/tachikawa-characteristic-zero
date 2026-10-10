import OAI.RingTheory.Tachikawa.InducedRegular
import OAI.RingTheory.Tachikawa.HomBimodule

/-! Characteristic-independent excerpt from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard

lemma finiteResolutionLift {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ) [P.IsKProjective] (M : FiniteModule k R)
    (v : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)) :
    ∃ f : P ⟶ M.projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' = v := by
  obtain ⟨f,hf⟩ := kProjective_chain_representative P M.projectiveResolution.cochainComplex
    (v ≫ inv (DerivedCategory.Q.map M.projectiveResolution.π'))
  refine ⟨f,?_⟩
  rw [hf]; simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]

lemma lift_composite_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q T S U : C} (a : P ⟶ Q) (b : Q ⟶ T) (p : Q ⟶ S) (r : T ⟶ U)
    (v : P ⟶ S) (w : S ⟶ U)
    (ha : F.map a ≫ F.map p = F.map v)
    (hb : F.map b ≫ F.map r = F.map p ≫ F.map w) :
    F.map (a ≫ b) ≫ F.map r = F.map (v ≫ w) := by
  rw [Functor.map_comp,Category.assoc,hb,← Category.assoc,ha,← Functor.map_comp]

namespace HomBimodule
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) (Z : ModuleCat S)
def underlyingLinearEquiv : obj (k := k) X Z ≃ₗ[k] (X →ₗ[k] Z) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by ext x; exact k_smul_apply X Z c f x
instance [FiniteDimensional k X] [FiniteDimensional k Z] : FiniteDimensional k (obj (k := k) X Z) :=
  Module.Finite.equiv (underlyingLinearEquiv X Z).symm
end HomBimodule
end Tachikawa
end
end OAI
