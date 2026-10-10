import TachikawaCharZero.InducedTensorHomology

/-! A finite model of evaluated Y built from the actual signed corner
total, together with its degree-five projective tail resolution.
The full stable-Hom W profile and branch normalization remain separate. -/
namespace TachikawaCharZero.CornerTensorModel
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped ModuleCat.Algebra
open ScalingSocle SocleBimodule InducedTensorComparison

def termEquiv (n : ℕ) : EvaluatedInduction.inducedSimpleChain.X n ≃ₗ[E]
    cornerTensorChain.X n :=
  ((HomologicalComplex.eval (ModuleCat E) (.down ℕ) n).mapIso inducedTensorIso).toLinearEquiv

theorem term_finite (n : ℕ) : Module.Finite E (cornerTensorChain.X n) := by
  let : Module.Finite E (EvaluatedInduction.inducedSimpleChain.X n) :=
    EvaluatedCokerComparison.induced_term_finite n
  exact Module.Finite.equiv (termEquiv n)

theorem term_projective (n : ℕ) : Module.Projective E (cornerTensorChain.X n) := by
  let : Module.Projective E (EvaluatedInduction.inducedSimpleChain.X n) :=
    EvaluatedCokerComparison.induced_term_projective n
  exact Module.Projective.of_equiv (termEquiv n)

def cokerEquiv (n : ℕ) :
    NatCoker.C EvaluatedInduction.inducedSimpleChain n ≃ₗ[E]
      NatCoker.C cornerTensorChain n :=
  cokerLinearEquiv _ _ (termEquiv (n+2)) (termEquiv (n+1))
    (ModuleCat.hom_ext_iff.mp (inducedTensorIso.hom.comm (n+2) (n+1)).symm)

def cokerFive : FiniteModule ℚ E where
  obj := ModuleCat.of E (NatCoker.C cornerTensorChain 4)
  finite := by
    let : Module.Finite E (cornerTensorChain.X 5) := term_finite 5
    exact Module.Finite.quotient E (LinearMap.range (cornerTensorChain.d 6 5).hom)

def degreeFiveComparison : StableEquiv (k := ℚ)
    EvaluatedSource.N_X.obj cokerFive.obj :=
  EvaluatedCokerComparison.degreeFiveComparison.trans
    (StableEquiv.ofLinearEquiv (cokerEquiv 4))

def Y : FiniteModule ℚ E := cokerFive.negative Starting.E_form 4

def fixedYComparison : StableEquiv (k := ℚ)
    (Enveloping.evalObj X FixedBimoduleY.Y.obj) Y.obj :=
  EvaluatedCosyzygy.fixedYComparison.trans
    (EvaluatedCokerComparison.negativeComparison Starting.E_form
      EvaluatedSource.N_X cokerFive degreeFiveComparison 4)

def lift (H : ℚ) (hH : H ≠ 0) : X ⟶ Y.obj :=
  ModuleCat.ofHom (fixedYComparison.hom.comp (FixedYEvaluation.evaluatedLift H hH).hom)

theorem lift_stable_ne_zero (H : ℚ) (hH : H ≠ 0) :
    stableClass (k := ℚ) (lift H hH).hom ≠ 0 := by
  intro hz
  apply FixedYEvaluation.evaluatedLift_stable_ne_zero H hH
  apply (fixedYComparison.post X).injective
  change stableClass (k := ℚ) (lift H hH).hom = _
  simpa only [map_zero] using hz

theorem Y_nonprojective : ¬ Module.Projective E Y.obj := by
  intro hp
  apply lift_stable_ne_zero 2 (by norm_num)
  apply (stableClass_eq_zero_iff _).mpr
  exact ⟨Y.obj,Y.finite,hp,(lift 2 (by norm_num)).hom,LinearMap.id,rfl⟩

def tailObj (n : ℕ) : ModuleCat E := cornerTensorChain.X (n+5)
def tailD (n : ℕ) : tailObj (n+1) ⟶ tailObj n := cornerTensorChain.d (n+6) (n+5)
def tailAug : tailObj 0 ⟶ cokerFive.obj := ModuleCat.ofHom (NatCoker.π cornerTensorChain 4)

theorem tailD_exact (n : ℕ) : Function.Exact (tailD (n+1)) (tailD n) := by
  have h := InducedTensorHomology.cornerTensor_exactAt (n+6)
    (by omega) (by omega) (by omega)
  rw [HomologicalComplex.exactAt_iff' _ (n+7) (n+6) (n+5)
    (by simp) (by simp)] at h
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h

theorem tailAug_exact : Function.Exact (tailD 0) tailAug := by
  intro x
  exact Submodule.Quotient.mk_eq_zero _

theorem tailAug_surjective : Function.Surjective tailAug :=
  Submodule.mkQ_surjective _

def projectiveResolution : ProjectiveResolution cokerFive.obj :=
  resolutionOfExact cokerFive.obj tailObj tailD tailAug tailD_exact
    tailAug_exact tailAug_surjective (fun n => by
      let : Module.Projective E (tailObj n) := term_projective (n+5)
      infer_instance)

end
end TachikawaCharZero.CornerTensorModel
