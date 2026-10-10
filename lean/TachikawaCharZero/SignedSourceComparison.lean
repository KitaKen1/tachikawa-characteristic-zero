import TachikawaCharZero.SignedInductionComparison
import TachikawaCharZero.TensorDualResolution
import OAI.RingTheory.Tachikawa.HighLift

/-! Compare the actual chosen B_theta resolution with the right-twist of
the regular bimodule resolution, then induce the comparison. No high-degree
exactness of untwisted induction is assumed by these constructions. -/
namespace TachikawaCharZero.SignedSourceComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

section Generic
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def twistedRegularIso (σ : R ≃ₐ[k] R) :
    (AlgebraInduction.res
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) σ.op).toAlgHom).obj
        (Enveloping.regular (k := k) (R := R)) ≅ Enveloping.twistedRegular σ :=
  (AddEquiv.toLinearEquiv
      (R := Enveloping.Alg k R R)
      (M := ↑((AlgebraInduction.res
        (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) σ.op).toAlgHom).obj
          (Enveloping.regular (k := k) (R := R))))
      (M₂ := ↑(Enveloping.twistedRegular σ))
      (by rfl)
      (by
        intro a x
        change Enveloping.action R
            ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) σ.op) a) x =
          Enveloping.action (AlgebraInduction.Bimod σ.toAlgHom) a x
        induction a using TensorProduct.inductionOn with
        | tmul r s => rfl
        | add a b ha hb =>
          simp only [map_add, LinearMap.add_apply, ha, hb])).toModuleIso

end Generic

open ScalingSocle SignedInductionComparison
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

abbrev regularResolution := Enveloping.regularResolution (k := ℚ) (R := ScalingSocle.B)

def sourceIso : signedRestrictionB.obj (Enveloping.regular (k := ℚ) (R := ScalingSocle.B)) ≅
    TwistedBimoduleObstruction.U :=
  twistedRegularIso TwistedFactorization.theta

instance signedRestrictionB_projective : signedRestrictionB.PreservesProjectiveObjects := by
  change (ModuleCat.restrictScalars SignedInductionSquare.rightTwistB.toRingEquiv.toRingHom).PreservesProjectiveObjects
  infer_instance

def transportedResolution : ProjectiveResolution TwistedBimoduleObstruction.U :=
  TensorDualResolution.transportResolution
    (signedRestrictionB.mapProjectiveResolution regularResolution) sourceIso

def sourceHomotopy : HomotopyEquiv InducedTwistedSocle.resolution.complex
    ((signedRestrictionB.mapHomologicalComplex (.down ℕ)).obj regularResolution.complex) :=
  ProjectiveResolution.homotopyEquiv InducedTwistedSocle.resolution transportedResolution

def inducedHomotopy : HomotopyEquiv
    ((InducedTwistedSocle.inductionFunctor.mapHomologicalComplex (.down ℕ)).obj
      InducedTwistedSocle.resolution.complex)
    (((InducedTwistedSocle.inductionFunctor ⋙ signedRestrictionE).mapHomologicalComplex (.down ℕ)).obj
      regularResolution.complex) :=
  (InducedTwistedSocle.inductionFunctor.mapHomotopyEquiv sourceHomotopy).trans
    (HomotopyEquiv.ofIso (chainComparison.app regularResolution.complex))

theorem sourceHomotopy_augmentation : sourceHomotopy.hom ≫ transportedResolution.π =
    InducedTwistedSocle.resolution.π :=
  ProjectiveResolution.homotopyEquiv_hom_π _ _

theorem induced_exactAt_iff (n : ℕ) :
    ((InducedTwistedSocle.inductionFunctor.mapHomologicalComplex (.down ℕ)).obj
      InducedTwistedSocle.resolution.complex).ExactAt n ↔
    (((InducedTwistedSocle.inductionFunctor ⋙ signedRestrictionE).mapHomologicalComplex (.down ℕ)).obj
      regularResolution.complex).ExactAt n := by
  rw [exactAt_iff_isZero_homology, exactAt_iff_isZero_homology]
  exact (inducedHomotopy.toHomologyIso n).isZero_iff

abbrev untwistedChain :=
  (InducedTwistedSocle.inductionFunctor.mapHomologicalComplex (.down ℕ)).obj
    regularResolution.complex

theorem induced_untwisted_exactAt_iff (n : ℕ) :
    ((InducedTwistedSocle.inductionFunctor.mapHomologicalComplex (.down ℕ)).obj
      InducedTwistedSocle.resolution.complex).ExactAt n ↔ untwistedChain.ExactAt n :=
  (induced_exactAt_iff n).trans
    (InductionTwistComparison.restriction_exactAt_iff
      SignedInductionSquare.rightTwistE.toAlgHom (.down ℕ) untwistedChain n)

theorem source_reflected_exact_of_untwisted (n : ℕ) (hn : 0 < n)
    (h : untwistedChain.ExactAt n) :
    Function.Exact ((reflectCochain InducedTwistedSocle.inducedComplex).d ((n:ℤ)+1) n)
      ((reflectCochain InducedTwistedSocle.inducedComplex).d n ((n:ℤ)-1)) := by
  have he := (induced_untwisted_exactAt_iff n).mpr h
  let K := (InducedTwistedSocle.inductionFunctor.mapHomologicalComplex (.down ℕ)).obj
    InducedTwistedSocle.resolution.complex
  have hK : K.ExactAt n := he
  rw [K.exactAt_iff' (n+1) n (n-1) ((ComplexShape.down ℕ).prev_eq' (by rfl))
    ((ComplexShape.down ℕ).next_eq' (by change n-1+1=n; omega))] at hK
  exact resolution_reflect_exact InducedTwistedSocle.resolution
    InducedTwistedSocle.inductionFunctor n hn
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hK)

end
end TachikawaCharZero.SignedSourceComparison
