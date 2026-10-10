import OAI.RingTheory.Tachikawa.EvaluationCokernels
import OAI.RingTheory.Tachikawa.InductionLeftComparison

/-! Characteristic-independent excerpts from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section


namespace Tachikawa.AlgebraInduction
open CategoryTheory CategoryTheory.Limits
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)

lemma res_map_exact (T : ShortComplex (ModuleCat.{0} S)) (h : T.Exact) :
    (T.map (res φ)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance : PreservesFiniteLimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out 2 4).mp (res_map_exact φ)
  exact h.1
instance : PreservesFiniteColimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out 2 4).mp (res_map_exact φ)
  exact h.2

end Tachikawa.AlgebraInduction

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

def rightEvaluation : ModuleCat Rᵐᵒᵖ ⥤ ModuleCat k where
  obj M := ModuleCat.of k (BalancedTensor.T (k := k) (R := R) (S := k) (M := M) (N := X))
  map f := ModuleCat.ofHom (BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    (f.hom.restrictScalars k) f.hom.map_smul)
  map_id M := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

instance : (rightEvaluation (k := k) X).Additive where
  map_add {M N f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := k) ((f m) + (g m)) x = _
    exact congrArg (fun h : X →ₗ[k] _ => h x) ((BalancedTensor.mk (k := k) (R := R)
      (S := k) (M := N) (N := X)).map_add (f m) (g m))

def rightObjEquiv (M : ModuleCat (Alg k S R)) :
    Obj M ≃ₗ[Rᵐᵒᵖ] (rightFunctor.obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightEvaluationEquiv (M : ModuleCat (Alg k S R)) :
    evalType X M ≃ₗ[k] (rightEvaluation (k := k) X).obj (rightFunctor.obj M) := by
  let e := (rightObjEquiv (k := k) M).restrictScalars k
  let f := BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    e.toLinearMap (rightObjEquiv (k := k) M).map_smul
  let g := BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    e.symm.toLinearMap (rightObjEquiv (k := k) M).symm.map_smul
  let t : BalancedTensor.T (k := k) (R := R) (S := k) (M := Obj M) (N := X) ≃ₗ[k]
      (rightEvaluation (k := k) X).obj (rightFunctor.obj M) :=
    { f with
      invFun := g
      left_inv x := by
        change g (f x) = x
        induction x using BalancedTensor.induction_on with
        | h0 => simp only [map_zero]
        | ht m x => rfl
        | ha x y hx hy => simp only [map_add, hx, hy]
      right_inv x := by
        change f (g x) = x
        induction x using BalancedTensor.induction_on with
        | h0 => simp only [map_zero]
        | ht m x => rfl
        | ha x y hx hy => simp only [map_add, hx, hy] }
  exact BalancedTensor.restrictEquiv.trans t

@[simp] lemma rightEvaluationEquiv_mk (M : ModuleCat (Alg k S R)) (m : Obj M) (x : X) :
    rightEvaluationEquiv (k := k) X M (BalancedTensor.mk m x) =
      BalancedTensor.mk (k := k) (R := R) (S := k) (N := X)
        (show rightFunctor.obj M from m) x := rfl

def evalScalarEquiv (M : ModuleCat (Alg k S R)) :
    (ModuleCat.restrictScalars (algebraMap k S)).obj (evalObj X M) ≃ₗ[k] evalType X M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k S c) • (show evalType X M from x) = c • (show evalType X M from x)
    exact IsScalarTower.algebraMap_smul S c (show evalType X M from x)

def rightEvaluationComparisonIso (M : ModuleCat (Alg k S R)) :
    (ModuleCat.restrictScalars (algebraMap k S)).obj (evalObj X M) ≅
      (rightEvaluation (k := k) X).obj (rightFunctor.obj M) :=
  LinearEquiv.toModuleIso ((evalScalarEquiv X M).trans (rightEvaluationEquiv (k := k) X M))

def rightEvaluationComparison :
    evaluation (k := k) (S := S) X ⋙ ModuleCat.restrictScalars (algebraMap k S) ≅
      rightFunctor (k := k) (R := S) (S := R) ⋙ rightEvaluation (k := k) X :=
  NatIso.ofComponents (rightEvaluationComparisonIso X) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change rightEvaluationEquiv X N
      (BalancedTensor.mapLeft (k := k) (R := R) (S := S) (N := X)
        (leftMap f) (fun r m => (rightMap f).map_smul r m) (show evalType X M from x)) =
      ((rightEvaluation (k := k) X).map (rightFunctor.map f)).hom
        (rightEvaluationEquiv X M x)
    induction (show evalType X M from x) using BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ht m y => rfl
    | ha x y hx hy => simp only [map_add, hx, hy])

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (X : ModuleCat R)

def regularEvalBilinear : Obj (regular (k := k) (R := R)) →ₗ[R] X →ₗ[k] X where
  toFun m :=
    { toFun := fun x => regularLeftEquiv m • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_add' m n := by ext x; exact add_smul _ _ x
  map_smul' r m := by
    ext x
    change (regularLeftEquiv (r • m)) • x = r • (regularLeftEquiv m • x)
    rw [map_smul,smul_eq_mul,mul_smul]

def regularEval : evalObj X (regular (k := k) (R := R)) ⟶ X :=
  ModuleCat.ofHom (BalancedTensor.lift (regularEvalBilinear X) (by
    intro r m x
    change (1 * ((show R from m) * r)) • x = (show R from m) • (r • x)
    rw [one_mul,mul_smul]))

lemma regularTensor_move (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (regular (k := k) (R := R))) (N := X)
      (show Obj (regular (k := k) (R := R)) from r) x =
    BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) (r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (regular (k := k) (R := R))) (N := X) r
    (show Obj (regular (k := k) (R := R)) from (1:R)) x
  have hm : MulOpposite.op r • (show Obj (regular (k := k) (R := R)) from (1:R)) =
      (show Obj (regular (k := k) (R := R)) from r) := by
    change 1 * (1 * r) = r
    rw [one_mul,one_mul]
  rw [hm] at hb
  exact hb

def regularEvalInv : X ⟶ evalObj X (regular (k := k) (R := R)) :=
  ModuleCat.ofHom
    { toFun := fun x => BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) (r • x) =
          r • BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) x
        rw [← regularTensor_move X r x]
        have hm : r • (show Obj (regular (k := k) (R := R)) from (1:R)) =
            (show Obj (regular (k := k) (R := R)) from r) := by
          change r * (1 * 1) = r
          rw [one_mul,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }

def regularEvalIso : evalObj X (regular (k := k) (R := R)) ≅ X where
  hom := regularEval X
  inv := regularEvalInv X
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R))
      ((show R from m) • x) = BalancedTensor.mk m x
    exact (regularTensor_move X (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    change (1:R) • x = x
    exact one_smul R x

end Tachikawa.Enveloping

namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)

def restrictionUnderlyingEquiv (X : ModuleCat.{0} S) :
    (AlgebraInduction.res φ).obj X ≃ₗ[k] X where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) • (show X from x) = (algebraMap k S c) • (show X from x)
    rw [φ.commutes]

def homBimoduleRestrictionEquiv (X Z : ModuleCat.{0} S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj (HomBimodule.obj (k := k) X Z) ≃ₗ[
      Enveloping.Alg k R R]
        HomBimodule.obj (k := k) ((AlgebraInduction.res φ).obj X) ((AlgebraInduction.res φ).obj Z) where
  toFun f := (restrictionUnderlyingEquiv φ Z).symm.toLinearMap.comp
    ((show X →ₗ[k] Z from f).comp (restrictionUnderlyingEquiv φ X).toLinearMap)
  invFun f := (restrictionUnderlyingEquiv φ Z).toLinearMap.comp
    ((show (AlgebraInduction.res φ).obj X →ₗ[k] (AlgebraInduction.res φ).obj Z from f).comp
      (restrictionUnderlyingEquiv φ X).symm.toLinearMap)
  left_inv f := by apply LinearMap.ext; intro x; rfl
  right_inv f := by apply LinearMap.ext; intro x; rfl
  map_add' f g := by apply LinearMap.ext; intro x; rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro x
    induction a using TensorProduct.inductionOn with
    | tmul r s => rfl
    | add a b ha hb =>
      change (show X →ₗ[k] Z from (Enveloping.envelopingMap φ (a+b)) •
        (show HomBimodule.obj (k := k) X Z from f)) x = _
      simp only [map_add]
      erw [add_smul, add_smul]
      exact congrArg₂ (fun u v => u+v) ha hb

def homBimoduleRestrictionIso (X Z : ModuleCat.{0} S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj (HomBimodule.obj (k := k) X Z) ≅
      HomBimodule.obj (k := k) ((AlgebraInduction.res φ).obj X) ((AlgebraInduction.res φ).obj Z) :=
  LinearEquiv.toModuleIso (homBimoduleRestrictionEquiv φ X Z)

def homBimoduleRestriction (X : ModuleCat.{0} S) :
    homBimoduleFunctor (k := k) X ⋙ AlgebraInduction.res (Enveloping.envelopingMap φ) ≅
      AlgebraInduction.res φ ⋙ homBimoduleFunctor (k := k) ((AlgebraInduction.res φ).obj X) :=
  NatIso.ofComponents (homBimoduleRestrictionIso φ X) (by
    intro Z Z' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro x
    rfl)

end Tachikawa

namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (X : ModuleCat.{0} R)

lemma regular_evaluation_quasiIso :
    QuasiIso (((evaluation (k := k) X).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := rightResolutionOf P (fun n => inferInstance)
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := regular_right_projective
  let : Projective ((rightFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of Rᵐᵒᵖ (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := rightEvaluation (k := k) X
  let T := rightFunctor (k := k) (R := R) (S := R)
  let T' : ModuleCat.{0} R ⥤ ModuleCat.{0} k := ModuleCat.restrictScalars (algebraMap k R)
  let : CategoryTheory.Limits.PreservesFiniteLimits T' :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteLimits
      (AlgebraInduction.res (k := k) (Algebra.ofId k R)))
  let : CategoryTheory.Limits.PreservesFiniteColimits T' :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteColimits
      (AlgebraInduction.res (k := k) (Algebra.ofId k R)))
  let J := evaluation (k := k) (S := R) X
  have h : QuasiIso ((I.mapHomologicalComplex _).map Q.π) :=
    Tachikawa.map_resolution_quasiIso I Q
  change QuasiIso ((I.mapHomologicalComplex _).map
    ((T.mapHomologicalComplex _).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _)) at h
  rw [Functor.map_comp] at h
  let := h
  have hI : QuasiIso ((I.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map P.π)) :=
    quasiIso_of_comp_right _ ((I.mapHomologicalComplex _).map
      ((HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _))
  have hJ :=
    (Tachikawa.quasiIso_map_natIso (rightEvaluationComparison (k := k) (S := R) X) P.π).mpr hI
  change QuasiIso ((T'.mapHomologicalComplex _).map ((J.mapHomologicalComplex _).map P.π)) at hJ
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def evaluatedRegularResolution : ProjectiveResolution X where
  complex := ((evaluation (k := k) X).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective (evalObj X ((regularResolution (k := k) (R := R)).complex.X n))
    infer_instance
  π := ((evaluation (k := k) X).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app _ ≫
        (ChainComplex.single₀ (ModuleCat R)).map (regularEvalIso (k := k) X).hom
  quasiIso := by
    let := regular_evaluation_quasiIso (k := k) X
    let : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app
          (regular (k := k) (R := R))) := inferInstance
    have regularQuasiIso : QuasiIso ((ChainComplex.single₀ (ModuleCat R)).map
        (regularEvalIso (k := k) X).hom) := quasiIso_of_isIso _
    let : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app
          (regular (k := k) (R := R)) ≫ (ChainComplex.single₀ (ModuleCat R)).map
            (regularEvalIso (k := k) X).hom) := quasiIso_comp _ _ (hφ' := regularQuasiIso)
    exact quasiIso_comp _ _

def evaluatedRegularComparison (P : ProjectiveResolution X) :
    HomotopyEquiv (evaluatedRegularResolution (k := k) X).complex P.complex :=
  ProjectiveResolution.homotopyEquiv _ _

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S) (X : ModuleCat.{0} S)

def inductionEvaluation :
    AlgebraInduction.functor (envelopingMap φ) ⋙ evaluation (k := k) (S := S) X ≅
      evaluation (k := k) (S := R) ((AlgebraInduction.res φ).obj X) ⋙
        AlgebraInduction.functor φ := by
  let a := (AlgebraInduction.adjunction (envelopingMap φ)).comp
    (evaluationAdjunction (k := k) (S := S) X)
  let b := (evaluationAdjunction (k := k) (S := R) ((AlgebraInduction.res φ).obj X)).comp
    (AlgebraInduction.adjunction φ)
  exact Adjunction.leftAdjointUniq (a.ofNatIsoRight (homBimoduleRestriction φ X)) b

variable [FiniteDimensional k R] [FiniteDimensional k S]

def evaluatedInducedRegularIso :
    ((evaluation (k := k) (S := S) X).mapHomologicalComplex _).obj (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ).mapHomologicalComplex _).obj
        (evaluatedRegularResolution (k := k) ((AlgebraInduction.res φ).obj X)).complex :=
  (NatIso.mapHomologicalComplex (inductionEvaluation φ X) (ComplexShape.down ℕ)).app
    (regularResolution (k := k) (R := R)).complex

def evaluatedInducedRegularComparison (P : ProjectiveResolution ((AlgebraInduction.res φ).obj X)) :
    HomotopyEquiv
      (((evaluation (k := k) (S := S) X).mapHomologicalComplex _).obj (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P.complex) :=
  (HomotopyEquiv.ofIso (evaluatedInducedRegularIso φ X)).trans
    ((AlgebraInduction.functor φ).mapHomotopyEquiv
      (evaluatedRegularComparison (k := k) ((AlgebraInduction.res φ).obj X) P))

end Tachikawa.Enveloping

end
end OAI
