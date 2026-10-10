import OAI.RingTheory.Tachikawa.OuterTensor
import OAI.RingTheory.Tachikawa.InductionAdjunction

/-! Characteristic-independent excerpt from OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T)
  (P : ChainComplex (ModuleCat A) ℕ) (Q : ChainComplex (ModuleCat B) ℕ)

abbrev outerDouble := ((bifunctor k A B).mapBifunctorHomologicalComplex
  (.down ℕ) (.down ℕ)).obj P |>.obj Q

abbrev inducedOuterDouble :=
  ((bifunctor k S T).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj
    (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P) |>.obj
    (((AlgebraInduction.functor ψ).mapHomologicalComplex _).obj Q)

def inductionDoubleComparison :
    TotalMap.map₂ (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ))
      (outerDouble P Q) ⟶ inducedOuterDouble φ ψ P Q :=
  HomologicalComplex₂.homMk (fun ij => inductionComparison φ ψ (P.X ij.1) (Q.X ij.2))
    (by
      intro i i' j _
      have h := (inductionComparison_natural φ ψ (P.X i) (Q.X j)
        (P.d i i') (𝟙 (Q.X j))).symm
      rw [(AlgebraInduction.functor ψ).map_id] at h
      exact h)
    (by
      intro i j j' _
      have h := (inductionComparison_natural φ ψ (P.X i) (Q.X j)
        (𝟙 (P.X i)) (Q.d j j')).symm
      rw [(AlgebraInduction.functor φ).map_id] at h
      exact h)

instance inductionDoubleComparison_isIso : IsIso (inductionDoubleComparison φ ψ P Q) := by
  have (i j : ℕ) : IsIso (((inductionDoubleComparison φ ψ P Q).f i).f j) := by
    change IsIso (inductionComparison φ ψ (P.X i) (Q.X j))
    rw [← inductionIso_hom]
    infer_instance
  have (i : ℕ) : IsIso ((inductionDoubleComparison φ ψ P Q).f i) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.Hom.isIso_of_components _

def inductionTotalIso :
    ((AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).mapHomologicalComplex _).obj
      (mapBifunctor P Q (bifunctor k A B) (.down ℕ)) ≅
    mapBifunctor
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P)
      (((AlgebraInduction.functor ψ).mapHomologicalComplex _).obj Q)
      (bifunctor k S T) (.down ℕ) := by
  let F := AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)
  letI : PreservesColimits F :=
    (AlgebraInduction.adjunction (Algebra.TensorProduct.map φ ψ)).leftAdjoint_preservesColimits
  exact (TotalMap.iso F (outerDouble P Q) (.down ℕ)).symm ≪≫
    HomologicalComplex₂.total.mapIso (asIso (inductionDoubleComparison φ ψ P Q)) (.down ℕ)

end Tachikawa.OuterTensor
end
end OAI
