import TachikawaCharZero.RestrictionDimension
import OAI.RingTheory.Tachikawa.ProjectiveReplacement

/-! The actual rational restriction of E-enveloping finite projectives has
projective dimension at most eight. Bounded perfect complexes therefore
have constructed projective replacements after restriction. The generic
replacement is reused from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The totalization finiteness argument adapts ReverseResolution.lean,
lines 1243-1248 and 1270-1287, at the same source commit. -/
namespace TachikawaCharZero.RestrictedPerfect
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open RestrictionDimension
open TensorDualResolution (transportResolution total_isZero_above)
open ScalingSocle (inclusionC inclusionB inclusionBE restriction)
abbrev A := RestrictionDimension.A
abbrev T := RestrictionDimension.T
abbrev B := RestrictionDimension.B
abbrev E := RestrictionDimension.E
abbrev BE := RestrictionDimension.BE
abbrev EE := RestrictionDimension.EE

section Generic
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

theorem total_finite (P : ChainComplex (ModuleCat A) ℕ)
    (Q : ChainComplex (ModuleCat B) ℕ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (n : ℕ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (OuterTensor.bifunctor k A B) (.down ℕ)).X n) := by
  let : Finite {ij : ℕ × ℕ // ij.1+ij.2=n} := by
    let f : {ij : ℕ × ℕ // ij.1+ij.2=n} → Fin (n+1) × Fin (n+1) := fun t =>
      (⟨t.val.1, by omega⟩, ⟨t.val.2, by omega⟩)
    exact Finite.of_injective f (by
      intro x y h
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h))
  let F := fun ij : {ij : ℕ × ℕ // ij.1+ij.2=n} =>
    ((OuterTensor.bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let (i : ℕ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℕ) : FiniteDimensional k (Q.X j) := hQ j
  have (t : {ij : ℕ × ℕ // ij.1+ij.2=n}) : Module.Finite (A ⊗[k] B) (F t) := by
    change Module.Finite (A ⊗[k] B) (OuterTensor.Obj k A B (P.X t.val.1) (Q.X t.val.2))
    let : FiniteDimensional k (OuterTensor.Obj k A B (P.X t.val.1) (Q.X t.val.2)) :=
      inferInstanceAs (FiniteDimensional k ((P.X t.val.1) ⊗[k] (Q.X t.val.2)))
    exact Module.Finite.of_restrictScalars_finite k _ _
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  exact Module.Finite.equiv
    ((biproduct.isoCoproduct F).symm ≪≫ ModuleCat.biproductIsoPi F).toLinearEquiv.symm

end Generic

abbrev opB := Aᵐᵒᵖ ⊗[ℚ] Aᵐᵒᵖ
abbrev opE := Tᵐᵒᵖ ⊗[ℚ] Tᵐᵒᵖ
def opTensorB : opB ≃ₐ[ℚ] Bᵐᵒᵖ := Algebra.TensorProduct.opAlgEquiv ℚ ℚ A A
def opTensorE : opE ≃ₐ[ℚ] Eᵐᵒᵖ := Algebra.TensorProduct.opAlgEquiv ℚ ℚ T T
abbrev rawRightInclusion : opB →ₐ[ℚ] opE := Algebra.TensorProduct.map inclusionC.op inclusionC.op
abbrev oppositeRestriction := AlgebraInduction.res opTensorB.symm.toAlgHom
instance oppositeRestriction_isEquivalence : oppositeRestriction.IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars opTensorB.symm.toRingEquiv.toRingHom).IsEquivalence
abbrev rawRightE := (AlgebraInduction.res rawRightInclusion).obj (ModuleCat.of opE opE)
abbrev rightE := (AlgebraInduction.res inclusionB.op).obj (ModuleCat.of Eᵐᵒᵖ Eᵐᵒᵖ)

theorem opposite_inclusion (x : opB) :
    opTensorE (rawRightInclusion x)=inclusionB.op (opTensorB x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b => rfl

def rightETargetIso : oppositeRestriction.obj rawRightE ≅ rightE :=
  LinearEquiv.toModuleIso (X₁ := oppositeRestriction.obj rawRightE) (X₂ := rightE)
    (m₁ := (oppositeRestriction.obj rawRightE).isModule) (m₂ := rightE.isModule)
    { toFun := opTensorE
      invFun := opTensorE.symm
      left_inv := opTensorE.left_inv
      right_inv := opTensorE.right_inv
      map_add' := opTensorE.map_add
      map_smul' r x := by
        change opTensorE (rawRightInclusion (opTensorB.symm r)*(show opE from x))=
          inclusionB.op r*opTensorE (show opE from x)
        rw [map_mul,opposite_inclusion,AlgEquiv.apply_symm_apply] }

def rawRightEResolution : CategoryTheory.ProjectiveResolution rawRightE :=
  transportResolution
    (TensorExt.resolution ℚ Aᵐᵒᵖ Aᵐᵒᵖ rightTResolution rightTResolution
      rightT_finite rightT_finite)
    (tensorRegularIso inclusionC.op inclusionC.op)

def rightEResolution : CategoryTheory.ProjectiveResolution rightE :=
  transportResolution (oppositeRestriction.mapProjectiveResolution rawRightEResolution)
    rightETargetIso

theorem rightE_above (n : ℕ) (hn : 4 < n) : IsZero (rightEResolution.complex.X n) :=
  oppositeRestriction.map_isZero
    (total_isZero_above _ _ 2 2 rightT_above rightT_above n hn)

theorem rightE_projectiveDimension : HasProjectiveDimensionLE rightE 4 :=
  resolution_pd rightEResolution 4 rightE_above

theorem leftE_finite (n : ℕ) : Module.Finite B (leftEResolution.complex.X n) :=
  total_finite _ _ leftT_finiteQ leftT_finiteQ n

theorem rightE_finiteQ (n : ℕ) : Module.Finite ℚ (rightEResolution.complex.X n) := by
  let : Module.Finite opB (rawRightEResolution.complex.X n) :=
    total_finite _ _ rightT_finiteQ rightT_finiteQ n
  let : Module.Finite ℚ (rawRightEResolution.complex.X n) := Module.Finite.trans opB _
  change Module.Finite ℚ (oppositeRestriction.obj (rawRightEResolution.complex.X n))
  infer_instance

theorem rightE_finite (n : ℕ) : Module.Finite Bᵐᵒᵖ (rightEResolution.complex.X n) := by
  let := rightE_finiteQ n
  exact Module.Finite.of_restrictScalars_finite ℚ Bᵐᵒᵖ _

abbrev restrictedRegular := restriction.obj (ModuleCat.of EE EE)
def envelopingResolution : CategoryTheory.ProjectiveResolution restrictedRegular :=
  transportResolution
    (TensorExt.resolution ℚ B Bᵐᵒᵖ leftEResolution rightEResolution leftE_finite rightE_finite)
    (Enveloping.restrictedOuterRegularIso inclusionB)

theorem enveloping_above (n : ℕ) (hn : 8 < n) :
    IsZero (envelopingResolution.complex.X n) :=
  total_isZero_above _ _ 4 4 leftE_above rightE_above n hn

theorem restrictedRegular_projectiveDimension : HasProjectiveDimensionLE restrictedRegular 8 :=
  resolution_pd envelopingResolution 8 enveloping_above

theorem restrictedProjective_pd (P : ModuleCat EE)
    [Module.Finite EE P] [Module.Projective EE P] :
    HasProjectiveDimensionLE (restriction.obj P) 8 := by
  let := restrictedRegular_projectiveDimension
  exact ((finiteProjective_inAdd P).map restriction).projectiveDimension 9

theorem bounded_replacement (P : CochainComplex (ModuleCat EE) ℤ)
    (hfin : ∀ i, Module.Finite EE (P.X i))
    (hproj : ∀ i, Module.Projective EE (P.X i))
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (Q : CochainComplex (ModuleCat BE) ℤ)
      (f : Q ⟶ (restriction.mapHomologicalComplex (.up ℤ)).obj P), QuasiIso f ∧
      (∀ i, Module.Projective BE (Q.X i)) ∧ (∀ i, Module.Finite BE (Q.X i)) ∧
      (∀ i, i < l-8 ∨ u < i → IsZero (Q.X i)) := by
  have hfin' (i : ℤ) : Module.Finite ℚ (restriction.obj (P.X i)) := by
    let := hfin i
    let : IsScalarTower ℚ EE (P.X i) :=
      ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ) (P.X i)
    let : Module.Finite ℚ (P.X i) := Module.Finite.trans EE _
    exact AlgebraInduction.resFinite _ _
  have hpd (i : ℤ) : HasProjectiveDimensionLE (restriction.obj (P.X i)) 8 := by
    let := hfin i
    let := hproj i
    exact restrictedProjective_pd (P.X i)
  obtain ⟨Q,f,hf,hp,hf',hb'⟩ := bounded_projective_replacement
    ((restriction.mapHomologicalComplex (.up ℤ)).obj P) 8 hfin' hpd l u
    (fun i hi => restriction.map_isZero (hb i hi))
  refine ⟨Q,f,hf,?_,?_,hb'⟩
  · intro i
    let := hp i
    infer_instance
  · intro i
    let := hf' i
    let : IsScalarTower ℚ BE (Q.X i) :=
      ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ) (Q.X i)
    exact Module.Finite.of_restrictScalars_finite ℚ BE _

end
end TachikawaCharZero.RestrictedPerfect
