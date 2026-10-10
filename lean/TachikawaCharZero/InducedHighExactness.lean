import TachikawaCharZero.SignedSourceComparison
import TachikawaCharZero.RestrictionDimension
import TachikawaCharZero.TwistedStableGate
import OAI.RingTheory.Tachikawa.InductionLeftComparison

/-! The actual length-four restricted E resolution supplies untwisted
high exactness. The signed-source comparison then removes the source
exactness hypothesis from the actual high stable-lift theorem. This does
not identify a fixed Y or prove nonzero tensor-Hom evaluation. -/
namespace TachikawaCharZero.InducedHighExactness
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open ScalingSocle InducedTwistedSocle TwistedSocleLifts
open scoped TensorProduct ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

abbrev sideInduction := AlgebraInduction.functor (k := ℚ)
  (R := ScalingSocle.B) (S := E) inclusionB

def untwistedLeftHomotopy :=
  Enveloping.inducedLeftHomotopy (k := ℚ) (R := ScalingSocle.B) (S := E)
    inclusionB RestrictionDimension.leftEResolution

theorem untwisted_high_exact (n : ℕ) (hn : 4 < n) :
    SignedSourceComparison.untwistedChain.ExactAt n := by
  let C := (sideInduction.mapHomologicalComplex (.down ℕ)).obj
    RestrictionDimension.leftEResolution.complex
  have hz : IsZero (C.X n) := sideInduction.map_isZero
    (RestrictionDimension.leftE_above n hn)
  have he : (Enveloping.leftComplex
      (Enveloping.inducedRegularComplex (k := ℚ) (R := ScalingSocle.B) (S := E) inclusionB)).ExactAt n :=
    (exactAt_iff_of_quasiIsoAt untwistedLeftHomotopy.hom n).mpr (ExactAt.of_isZero hz)
  exact (InductionTwistComparison.restriction_exactAt_iff
    (Algebra.TensorProduct.includeLeft : E →ₐ[ℚ] EE) (.down ℕ)
    SignedSourceComparison.untwistedChain n).mp he

theorem signed_high_exact (n : ℕ) (hn : 4 < n) :
    Function.Exact ((reflectCochain inducedComplex).d ((n:ℤ)+1) n)
      ((reflectCochain inducedComplex).d n ((n:ℤ)-1)) :=
  SignedSourceComparison.source_reflected_exact_of_untwisted n (by omega)
    (untwisted_high_exact n hn)

theorem lift_stable_ne_zero (H : ℚ) (hH : H ≠ 0)
    (f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex)
    (hf : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
      DerivedCategory.Q.map (inducedSocleMap H hH)) (n : ℕ) (hn : 5 ≤ n) :
    stableClass (k := ℚ) (CokerAt.map (reflectCochainMap f) n) ≠ 0 :=
  TwistedStableGate.lift_stable_ne_zero_of_source_exact H hH 5 (by omega)
    (fun m hm => signed_high_exact m (by omega)) f hf n hn

theorem exists_stable_lift (H : ℚ) (hH : H ≠ 0) :
    ∃ f : inducedComplex ⟶ (finiteU H hH).projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap H hH) ∧
      ∀ n : ℕ, 5 ≤ n → stableClass (k := ℚ) (CokerAt.map (reflectCochainMap f) n) ≠ 0 :=
  TwistedStableGate.exists_stable_lift_of_source_exact H hH 5 (by omega)
    (fun n hn => signed_high_exact n (by omega))

end
end TachikawaCharZero.InducedHighExactness
