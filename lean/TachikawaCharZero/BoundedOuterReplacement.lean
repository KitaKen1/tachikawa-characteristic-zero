import TachikawaCharZero.BInjectiveDimension
import TachikawaCharZero.TwistedFactorization
import OAI.RingTheory.Tachikawa.FiniteOuterReplacement

/-! A bounded outer replacement for every actual finite projective
rational B-bimodule complex. Four coinduced cokernels suffice because
the regular left B-module has checked injective dimension at most four.
Support [l,u] grows only to [l,u+4]. This specializes characteristic-
independent arguments from OpenAI Math's FiniteCoinduction.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.BoundedOuterReplacement
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open TwistedFactorization

abbrev BE := Enveloping.Alg ℚ B₀ B₀
abbrev regular := Enveloping.leftRegularObj (R := B₀)
abbrev outer := Enveloping.ordinaryOuterObj (k := ℚ) (R := B₀)

instance regular_finite : FiniteDimensional ℚ regular :=
  Module.Finite.equiv (Enveloping.leftRegularUnderlying (k := ℚ) (R := B₀)).symm

theorem iterate_injective : Injective ((LeftCoinduced.iterate (k := ℚ) 4).obj regular) := by
  let : HasInjectiveDimensionLE regular 4 := BInjectiveDimension.regular_injectiveDimension
  exact LeftCoinduced.iterate_injective regular 4

theorem iterate_inAdd : InAdd (Enveloping.dualLeftObj (k := ℚ) (R := B₀))
    ((LeftCoinduced.iterate (k := ℚ) 4).obj regular) := by
  let := iterate_injective
  exact finiteInjective_inAdd _

theorem leftTerm_inAdd (n : ℕ) : InAdd (Enveloping.dualLeftObj (k := ℚ) (R := B₀))
    ((LeftCoinduced.J (k := ℚ)).obj ((LeftCoinduced.iterate (k := ℚ) n).obj regular)) :=
  finiteInjective_inAdd _

theorem outerTerm_inAdd (n : ℕ) : InAdd outer
    (Enveloping.coindTerm (Enveloping.rightFreeObj (k := ℚ) (S := B₀) regular) n) :=
  ((leftTerm_inAdd n).map (Enveloping.rightFreeFunctor (k := ℚ) (S := B₀))).iso
    (Enveloping.coindTermTensorIso regular n).symm

theorem outerIterate_inAdd : InAdd outer
    ((Enveloping.coindIterate (k := ℚ) 4).obj
      (Enveloping.rightFreeObj (k := ℚ) (S := B₀) regular)) :=
  (iterate_inAdd.map (Enveloping.rightFreeFunctor (k := ℚ) (S := B₀))).iso
    (Enveloping.coindIterateTensorIso regular 4).symm

theorem projective_coinduced_terms (L : ModuleCat BE)
    [Module.Finite BE L] [Module.Projective BE L] :
    (∀ n : ℕ, InAdd outer (Enveloping.coindTerm L n)) ∧
    InAdd outer ((Enveloping.coindIterate (k := ℚ) 4).obj L) := by
  have hL : InAdd (Enveloping.rightFreeObj (k := ℚ) (S := B₀) regular) L :=
    Enveloping.finiteProjective_inAdd_outer L
  constructor
  · intro n
    exact (outerTerm_inAdd n).trans
      (hL.map (Enveloping.coindIterate (k := ℚ) n ⋙ Enveloping.coindEndo))
  · exact outerIterate_inAdd.trans (hL.map (Enveloping.coindIterate (k := ℚ) 4))

theorem coindGoodTerms (P : CochainComplex (ModuleCat BE) ℤ)
    (hfin : ∀ i, Module.Finite BE (P.X i))
    (hproj : ∀ i, Module.Projective BE (P.X i)) :
    Enveloping.CoindGoodTerms outer 4 P := by
  have h (i : ℤ) := by
    let := hfin i
    let := hproj i
    exact projective_coinduced_terms (P.X i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; exact (h i).1 0
  · intro i; exact (h i).1 1
  · intro i; exact (h i).1 2
  · intro i; exact (h i).1 3
  · intro i; exact (h i).2

theorem bounded_ordinary_replacement (P : CochainComplex (ModuleCat BE) ℤ)
    (hfin : ∀ i, Module.Finite BE (P.X i))
    (hproj : ∀ i, Module.Projective BE (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (P' : CochainComplex (ModuleCat BE) ℤ) (f : P ⟶ P'),
      QuasiIso f ∧ (∀ i, InAdd outer (P'.X i)) ∧
      (∀ i, i < l ∨ u+4 < i → IsZero (P'.X i)) := by
  refine ⟨(Enveloping.coindReplacement 4 P).complex,
    (Enveloping.coindReplacement 4 P).map,inferInstance,?_,?_⟩
  · exact Enveloping.coindReplacement_terms outer 4 P (coindGoodTerms P hfin hproj)
  · exact Enveloping.coindReplacement_bounded 4 P l u hbound

end
end TachikawaCharZero.BoundedOuterReplacement
