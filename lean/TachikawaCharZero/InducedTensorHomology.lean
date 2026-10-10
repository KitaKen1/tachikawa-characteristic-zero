import TachikawaCharZero.InducedTensorComparison

/-! The evaluated actual source is exact in every degree outside 0, 2,
and 4. The argument splits complexes only after forgetting to rational
vector spaces, where splitting is valid, and reflects exactness back to
E-modules. It does not assert that induction is exact. -/
namespace TachikawaCharZero.InducedTensorHomology
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open InducedTensorComparison

theorem restrict_exactAt_iff {R S : Type} [Ring R] [Ring S]
    (f : R →+* S) {ι : Type} (c : ComplexShape ι)
    (P : HomologicalComplex (ModuleCat S) c) (n : ι) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj P).ExactAt n ↔
      P.ExactAt n :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).trans
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (P.sc n)).symm

abbrev vectorJ := ((OuterTensor.forgetA ℚ ScalingSocle.T).mapHomologicalComplex
  (.down ℕ)).obj Induced.complex

theorem vectorJ_exactAt (n : ℕ) (hn₀ : n≠0) (hn₂ : n≠2) : vectorJ.ExactAt n :=
  (restrict_exactAt_iff (algebraMap ℚ ScalingSocle.T) (.down ℕ)
    Induced.complex n).mpr (Induced.complex_exactAt n hn₀ hn₂)

theorem vectorJ_homology_isZero (n : ℕ) (hn₀ : n≠0) (hn₂ : n≠2) :
    IsZero (ModuleCat.of ℚ (VectorSplit.H vectorJ n)) :=
  (TensorExt.homologyIsoH vectorJ n).isZero_iff.mp
    (vectorJ_exactAt n hn₀ hn₂).isZero_homology

abbrev vectorTensor := mapBifunctor vectorJ vectorJ
  (VectorSplit.tensorFunctor (k := ℚ)) (.down ℕ)
abbrev homologyTensor := mapBifunctor (VectorSplit.homologyComplex vectorJ)
  (VectorSplit.homologyComplex vectorJ)
  (VectorSplit.tensorFunctor (k := ℚ)) (.down ℕ)

theorem homologyTensor_isZero (n : ℕ) (hn₀ : n≠0) (hn₂ : n≠2) (hn₄ : n≠4) :
    IsZero (homologyTensor.X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j h
  rw [Category.comp_id,comp_zero]
  have hij : i+j=n := h
  by_cases hi : i=0 ∨ i=2
  · have hj₀ : j≠0 := by rcases hi with hi | hi <;> omega
    have hj₂ : j≠2 := by rcases hi with hi | hi <;> omega
    exact (((VectorSplit.tensorFunctor (k := ℚ)).obj _).map_isZero
      (vectorJ_homology_isZero j hj₀ hj₂)).eq_of_src _ _
  · have hi₀ : i≠0 := fun h => hi (Or.inl h)
    have hi₂ : i≠2 := fun h => hi (Or.inr h)
    exact (((VectorSplit.tensorFunctor (k := ℚ)).flip.obj _).map_isZero
      (vectorJ_homology_isZero i hi₀ hi₂)).eq_of_src _ _

theorem vectorTensor_homology_isZero (n : ℕ)
    (hn₀ : n≠0) (hn₂ : n≠2) (hn₄ : n≠4) : IsZero (vectorTensor.homology n) :=
  (VectorSplit.tensorHomologyIso vectorJ vectorJ (.down ℕ) n).isZero_iff.mpr
    (homologyTensor_isZero n hn₀ hn₂ hn₄)

def vectorTensorIso :
    ((OuterTensor.forgetE ℚ ScalingSocle.T ScalingSocle.T).mapHomologicalComplex
      (.down ℕ)).obj cornerTensorChain ≅ vectorTensor :=
  OuterTensor.forgetTotalIso ℚ ScalingSocle.T ScalingSocle.T
    Induced.complex Induced.complex (.down ℕ)

theorem cornerTensor_exactAt (n : ℕ) (hn₀ : n≠0) (hn₂ : n≠2) (hn₄ : n≠4) :
    cornerTensorChain.ExactAt n := by
  apply (restrict_exactAt_iff (algebraMap ℚ ScalingSocle.E)
    (.down ℕ) cornerTensorChain n).mp
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctor (ModuleCat ℚ) (.down ℕ) n).mapIso
    vectorTensorIso).isZero_iff.mpr
      (vectorTensor_homology_isZero n hn₀ hn₂ hn₄)

theorem evaluated_exactAt (n : ℕ) (hn₀ : n≠0) (hn₂ : n≠2) (hn₄ : n≠4) :
    EvaluatedCokerComparison.chosenEvaluatedChain.ExactAt n :=
  (InducedTensorComparison.evaluated_exactAt_iff n).mpr
    (cornerTensor_exactAt n hn₀ hn₂ hn₄)

theorem evaluated_tail_exact (n : ℕ) (hn : 4<n) :
    EvaluatedCokerComparison.chosenEvaluatedChain.ExactAt n :=
  evaluated_exactAt n (by omega) (by omega) (by omega)

end
end TachikawaCharZero.InducedTensorHomology
