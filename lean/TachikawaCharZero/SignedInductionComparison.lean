import TachikawaCharZero.SignedInductionSquare
import TachikawaCharZero.InductionTwistComparison

/-! Restriction along the actual right-twist automorphisms commutes with
induction, up to a natural isomorphism constructed by uniqueness of left
adjoints. This also compares the mapped complexes. Source exactness is a
separate obligation. -/
namespace TachikawaCharZero.SignedInductionComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra



open ScalingSocle SignedInductionSquare
local instance beRing : Ring BE := InducedTwistedSocle.beRing
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

abbrev signedRestrictionB := AlgebraInduction.res rightTwistB.toAlgHom
abbrev signedRestrictionE := AlgebraInduction.res rightTwistE.toAlgHom

def comparison : signedRestrictionB ⋙ InducedTwistedSocle.inductionFunctor ≅
    InducedTwistedSocle.inductionFunctor ⋙ signedRestrictionE :=
  InductionTwistComparison.inductionComparison (k := ℚ) (R := BE) (S := EE)
    inclusionBE rightTwistB rightTwistE inclusion_square

def chainComparison :
    (signedRestrictionB ⋙ InducedTwistedSocle.inductionFunctor).mapHomologicalComplex (.down ℕ) ≅
      (InducedTwistedSocle.inductionFunctor ⋙ signedRestrictionE).mapHomologicalComplex (.down ℕ) :=
  NatIso.mapHomologicalComplex comparison (.down ℕ)

def cochainComparison :
    (signedRestrictionB ⋙ InducedTwistedSocle.inductionFunctor).mapHomologicalComplex (.up ℤ) ≅
      (InducedTwistedSocle.inductionFunctor ⋙ signedRestrictionE).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex comparison (.up ℤ)

end
end TachikawaCharZero.SignedInductionComparison
