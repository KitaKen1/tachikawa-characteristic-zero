import TachikawaCharZero.TwistedSocleLifts
import OAI.RingTheory.Tachikawa.HighLift

/-! Actual rational E-enveloping symmetry, derived nonzero socle lifts,
and finite source cokernels. The high stable conclusion is conditional
only on exactness of the signed induced source in sufficiently high degrees.
No such source exactness or fixed-Y evaluation is asserted here. -/
namespace TachikawaCharZero.TwistedStableGate
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open ScalingSocle SocleBimodule InducedTwistedSocle TwistedSocleLifts
open scoped TensorProduct ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def envelopingForm : SymmetrizingForm (k := ℚ) (R := EE) :=
  SymmetricTensor.form Starting.E_form Starting.E_form.op

theorem EE_symmetric : SymmetricOver ℚ EE := envelopingForm.symmetricOver

theorem EE_injective : Module.Injective EE EE := envelopingForm.injective

theorem EE_finrank : Module.finrank ℚ EE = 160000 := by
  have ho : Module.finrank ℚ Eᵐᵒᵖ = 400 :=
    (MulOpposite.opLinearEquiv ℚ : E ≃ₗ[ℚ] Eᵐᵒᵖ).symm.finrank_eq.trans
      Starting.E_finrank
  change Module.finrank ℚ (E ⊗[ℚ] Eᵐᵒᵖ) = 160000
  rw [Module.finrank_tensorProduct,Starting.E_finrank,ho]

theorem inducedSocle_derived_ne_zero (H : ℚ) (hH : H ≠ 0) :
    DerivedCategory.Q.map (inducedSocleMap H hH) ≠ 0 := by
  let P : CochainComplex (ModuleCat EE) ℤ := HomologicalComplex.zero
  have hP : IsZero P := HomologicalComplex.isZero_zero
  have hzero (i : ℤ) : IsZero (P.X i) :=
    (HomologicalComplex.eval (ModuleCat EE) (.up ℤ) i).map_isZero hP
  have hfin (i : ℤ) : Module.Finite EE (P.X i) := by
    let : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp (hzero i)
    infer_instance
  have hproj (i : ℤ) : Module.Projective EE (P.X i) := by
    let : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp (hzero i)
    infer_instance
  have hb (i : ℤ) (_ : i < (0:ℤ) ∨ (0:ℤ) < i) : IsZero (P.X i) := hzero i
  have h := inducedSocle_not_bounded_projective_factor H hH P hfin hproj 0 0 hb 0 0
  exact Ne.symm (by simpa using h)

theorem representation_derived_ne_zero : DerivedCategory.Q.map representation ≠ 0 := by
  intro hz
  apply inducedSocle_derived_ne_zero 1 one_ne_zero
  simp only [inducedSocleMap,Functor.map_comp,hz,zero_comp]

theorem socle_lift_derived_ne_zero (H : ℚ) (hH : H ≠ 0)
    (f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex)
    (hf : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
      DerivedCategory.Q.map (inducedSocleMap H hH)) :
    DerivedCategory.Q.map f ≠ 0 := by
  intro hz
  apply inducedSocle_derived_ne_zero H hH
  rw [← hf,hz,zero_comp]

theorem socle_lift_ne_zero (H : ℚ) (hH : H ≠ 0)
    (f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex)
    (hf : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
      DerivedCategory.Q.map (inducedSocleMap H hH)) : f ≠ 0 := by
  intro hz
  apply socle_lift_derived_ne_zero H hH f hf
  simp only [hz,Functor.map_zero]

theorem source_coker_finite (n : ℤ) :
    Module.Finite EE (CokerAt (reflectCochain inducedComplex) n) := by
  let : Module.Finite EE ((reflectCochain inducedComplex).X n) := induced_term_finite (-n)
  exact Module.Finite.of_surjective (CokerAt.π (reflectCochain inducedComplex) n)
    (CokerAt.π_surjective _ _)

def sourceCoker (n : ℤ) : FiniteModule ℚ EE :=
  ⟨ModuleCat.of EE (CokerAt (reflectCochain inducedComplex) n), source_coker_finite n⟩

theorem target_reflect_exact (H : ℚ) (hH : H ≠ 0) (n : ℕ) (hn : 0 < n) :
    Function.Exact ((reflectCochain (finiteU H hH).projectiveResolution.cochainComplex).d
      ((n:ℤ)+1) n)
      ((reflectCochain (finiteU H hH).projectiveResolution.cochainComplex).d n ((n:ℤ)-1)) :=
  projectiveResolution_reflect_exact (finiteU H hH).projectiveResolution n hn

theorem lift_stable_ne_zero_of_source_exact (H : ℚ) (hH : H ≠ 0)
    (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hex : ∀ n : ℕ, n₀ ≤ n → Function.Exact ((reflectCochain inducedComplex).d ((n:ℤ)+1) n)
      ((reflectCochain inducedComplex).d n ((n:ℤ)-1)))
    (f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex)
    (hf : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
      DerivedCategory.Q.map (inducedSocleMap H hH))
    (n : ℕ) (hn : n₀ ≤ n) :
    stableClass (k := ℚ) (CokerAt.map (reflectCochainMap f) n) ≠ 0 := by
  let : Module.Injective EE EE := EE_injective
  have h := stably_nonzero_high_lift inducedComplex induced_term_projective
    (finiteU H hH) (inducedSocleMap H hH) n₀ hn₀ hex
    (inducedSocle_not_bounded_projective_factor H hH) f hf n hn
  intro hz
  exact h ((stableClass_eq_zero_iff _).mp hz)

theorem exists_stable_lift_of_source_exact (H : ℚ) (hH : H ≠ 0)
    (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hex : ∀ n : ℕ, n₀ ≤ n → Function.Exact ((reflectCochain inducedComplex).d ((n:ℤ)+1) n)
      ((reflectCochain inducedComplex).d n ((n:ℤ)-1))) :
    ∃ f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap H hH) ∧
      ∀ n : ℕ, n₀ ≤ n → stableClass (k := ℚ) (CokerAt.map (reflectCochainMap f) n) ≠ 0 := by
  obtain ⟨f,hf⟩ := exists_socle_lift H hH
  exact ⟨f,hf,fun n hn => lift_stable_ne_zero_of_source_exact H hH n₀ hn₀ hex f hf n hn⟩

end
end TachikawaCharZero.TwistedStableGate
