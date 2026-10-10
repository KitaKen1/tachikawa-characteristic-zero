import OAI.RingTheory.Tachikawa.EvaluationProjectivity
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R)

def homBimoduleFunctor : ModuleCat.{0} S ⥤ ModuleCat.{0} (Enveloping.Alg k S R) where
  obj Z := HomBimodule.obj (k := k) X Z
  map g := HomBimodule.postMap X g
  map_id Z := by ext f; rfl
  map_comp g h := by ext f; rfl

def evaluationAdjunction : Enveloping.evaluation (k := k) (S := S) X ⊣
    homBimoduleFunctor (k := k) (S := S) X :=
  Adjunction.mkOfHomEquiv
  { homEquiv := fun M Z => (BimoduleTensorHom.equiv (M := M) (X := X) (Z := Z)).toEquiv.symm
    homEquiv_naturality_left_symm := by
      intro M M' Z f g
      exact BimoduleTensorHom.uncurry_precompose f g
    homEquiv_naturality_right := by
      intro M Z Z' f g
      apply (BimoduleTensorHom.equiv (M := M) (X := X) (Z := Z')).injective
      change BimoduleTensorHom.uncurry (BimoduleTensorHom.curry (f ≫ g)) =
        BimoduleTensorHom.uncurry (BimoduleTensorHom.curry f ≫ HomBimodule.postMap X g)
      exact (BimoduleTensorHom.uncurry_curry (f ≫ g)).trans
        ((congrArg (fun h => h ≫ g) (BimoduleTensorHom.uncurry_curry f)).symm.trans
          (BimoduleTensorHom.uncurry_postcompose (BimoduleTensorHom.curry f) g).symm) }

end Tachikawa


namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R)

def evalCokerIso {M N : ModuleCat.{0} (Alg k S R)} (f : M ⟶ N) :
    evalObj (k := k) X (ModuleCat.of _ (N ⧸ LinearMap.range f.hom)) ≅
      ModuleCat.of S (evalObj (k := k) X N ⧸ LinearMap.range (evalMap (k := k) X f).hom) := by
  let : PreservesColimits (evaluation (k := k) (S := S) X) :=
    (evaluationAdjunction (k := k) X).leftAdjoint_preservesColimits
  exact (evaluation (k := k) X).mapIso (ModuleCat.cokernelIsoRangeQuotient f).symm ≪≫
    PreservesCokernel.iso (evaluation (k := k) X) f ≪≫ ModuleCat.cokernelIsoRangeQuotient (evalMap (k := k) X f)

end Tachikawa.Enveloping

end
end OAI
