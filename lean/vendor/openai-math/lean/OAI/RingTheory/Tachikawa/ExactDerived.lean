import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Generic exact derived morphism comparison from OpenAI Math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0.
Declarations are unchanged; imports and outer namespace are adapted. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def exactDerivedHom {X Y : CochainComplex C ℤ}
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj X) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Y) :=
  F.mapDerivedCategoryFactors.inv.app X ≫ F.mapDerivedCategory.map f ≫
    F.mapDerivedCategoryFactors.hom.app Y

lemma exactDerivedHom_comp {X Y Z : CochainComplex C ℤ}
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y)
    (g : DerivedCategory.Q.obj Y ⟶ DerivedCategory.Q.obj Z) :
    exactDerivedHom F (f ≫ g) = exactDerivedHom F f ≫ exactDerivedHom F g := by
  simp only [exactDerivedHom,Functor.map_comp,Category.assoc,
    Iso.hom_inv_id_app_assoc]

lemma exactDerivedHom_map {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    exactDerivedHom F (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  dsimp only [exactDerivedHom]
  rw [F.mapDerivedCategoryFactors_hom_naturality,Iso.inv_hom_id_app_assoc]

end Tachikawa
end
end OAI
