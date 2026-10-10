import TachikawaCharZero.BoundedOuterReplacement
import TachikawaCharZero.TwistedOrthogonality
import OAI.RingTheory.Tachikawa.OrthogonalDescent

/-! The actual rational twisted eta cannot factor in the derived category
through any bounded complex of finite projective B-bimodules. The bounded
outer replacement and both Ext orthogonalities are proved inputs, not
assumptions about an unconstructed replacement. Stable bimodule lifts
and evaluation at the final complete resolution remain separate.
The generic bounded descent is reused from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.TwistedDerivedObstruction
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open TwistedFactorization TwistedBimoduleObstruction
attribute [local instance] HasDerivedCategory.standard

def sourceFinite : FiniteModule ℚ BE := by
  let : IsScalarTower ℚ BE U := ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ) U
  let : Module.Finite BE U := Module.Finite.of_restrictScalars_finite ℚ BE U
  exact ⟨U,inferInstance⟩

def sourceResolution : ProjectiveResolution U := sourceFinite.projectiveResolution
abbrev sourceSingle := (CochainComplex.singleFunctor (ModuleCat BE) 0).obj U
abbrev targetSingle := (CochainComplex.singleFunctor (ModuleCat BE) 0).obj D

theorem ordinary_factorization (P : CochainComplex (ModuleCat BE) ℤ)
    (hfin : ∀ i, Module.Finite BE (P.X i))
    (hproj : ∀ i, Module.Projective BE (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (v : U ⟶ D)
    (α : DerivedCategory.Q.obj sourceSingle ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj targetSingle)
    (hv : α ≫ β = DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (ModuleCat BE) 0).map v)) :
    ∃ (V : ModuleCat BE) (a : U ⟶ V) (b : V ⟶ D),
      TwistedBimoduleObstruction.InAdd W V ∧ a ≫ b = v := by
  obtain ⟨P',f,hf,ht,hb⟩ :=
    BoundedOuterReplacement.bounded_ordinary_replacement P hfin hproj l u hbound
  let := hf
  have ht' (i : ℤ) : OAI.Tachikawa.InAdd W (P'.X i) := by
    change TwistedBimoduleObstruction.InAdd W (P'.X i)
    exact TwistedOrthogonality.inAdd_ordinary_to_outer (ht i)
  have he : (α ≫ DerivedCategory.Q.map f) ≫ (inv (DerivedCategory.Q.map f) ≫ β) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat BE) 0).map v) := by
    simpa only [Category.assoc,IsIso.hom_inv_id_assoc] using hv
  obtain ⟨a,b,hab⟩ := bounded_ordinary_factorization sourceResolution (injectiveResolution D)
    P' l (u+4) hb ht' TwistedOrthogonality.twisted_outer_ext_zero
    TwistedOrthogonality.outer_dual_ext_zero v
    (α ≫ DerivedCategory.Q.map f) (inv (DerivedCategory.Q.map f) ≫ β) he
  exact ⟨P'.X 0,a,b,ht' 0,hab⟩

theorem eta_not_bounded_projective_factor (P : CochainComplex (ModuleCat BE) ℤ)
    (hfin : ∀ i, Module.Finite BE (P.X i))
    (hproj : ∀ i, Module.Projective BE (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj sourceSingle ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj targetSingle) :
    α ≫ β ≠ DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (ModuleCat BE) 0).map etaMap) := by
  intro hv
  obtain ⟨V,a,b,hV,hab⟩ := ordinary_factorization P hfin hproj l u hbound etaMap α β hv
  exact etaMap_not_inAdd_factor hV a b hab

end
end TachikawaCharZero.TwistedDerivedObstruction
