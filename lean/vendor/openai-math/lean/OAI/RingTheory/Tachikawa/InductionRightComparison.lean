import OAI.RingTheory.Tachikawa.InductionLeftComparison

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
omit [FiniteDimensional k S] in
lemma left_induction_regular_quasiIso (φ : R →ₐ[k] S) :
    QuasiIso (((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := leftResolutionOf P (fun n => inferInstance)
  let : Module.Projective R (Obj (regular (k := k) (R := R))) := regular_left_projective
  let : Projective ((leftFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of R (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := AlgebraInduction.functor φ
  let T := leftFunctor (k := k) (R := R) (S := R)
  let T' := leftFunctor (k := k) (R := S) (S := R)
  let J := AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)
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
  have hB : QuasiIso (((leftIndFunctor (U := R) φ ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (leftIndUnderlyingComparison (U := R) φ) P.π).mpr hI
  have hJ : QuasiIso (((J ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (Functor.isoWhiskerRight (leftIndComparison (U := R) φ) T') P.π).mpr hB
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def leftInducedResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      (regular (k := k) (R := R))) where
  complex := ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  π := ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := by
    let := left_induction_regular_quasiIso φ
    infer_instance

end Tachikawa.Enveloping

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev rightRestrictedRegular (φ : R →ₐ[k] S) : ModuleCat (Alg k S R) :=
  ofBimodule (k := k) (R := S) (S := R) (AlgebraInduction.Bimod φ)

def regularLeftUnitTarget (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (leftEnvelopingMap (U := R) φ)).obj (rightRestrictedRegular φ) :=
  ModuleCat.ofHom (X := regular (k := k) (R := R))
    (Y := (AlgebraInduction.res (leftEnvelopingMap (U := R) φ)).obj (rightRestrictedRegular φ))
  { toFun := fun r => φ r
    map_add' := φ.map_add
    map_smul' a x := by
      change φ ((action (k := k) (R := R) (S := R) R a) x) =
        (action (k := k) (R := S) (S := R) (AlgebraInduction.Bimod φ) (leftEnvelopingMap φ a)) (φ x)
      induction a using TensorProduct.inductionOn with
      | tmul r s =>
        change φ (r * ((show R from x) * s.unop)) = φ r * (φ x * φ s.unop)
        rw [map_mul, map_mul]
      | add a b ha hb =>
        rw [map_add, map_add, map_add]
        change φ ((action (k := k) (R := R) (S := R) R a) x +
          (action (k := k) (R := R) (S := R) R b) x) = _
        exact (φ.map_add _ _).trans
          (congrArg₂ (fun x y : AlgebraInduction.Bimod φ => x+y) ha hb) }

def leftIndRegularHom (φ : R →ₐ[k] S) :
    leftIndObj φ (regular (k := k) (R := R)) ⟶ rightRestrictedRegular φ :=
  leftIndExtend φ (regularLeftUnitTarget φ)

lemma leftIndRegularHom_mk (φ : R →ₐ[k] S) (s : AlgebraInduction.Bimod φ)
    (r : Obj (regular (k := k) (R := R))) :
    (show S from leftIndRegularHom φ (BalancedTensor.mk s r)) = (show S from s) * φ r := by
  change (show S from s) * (φ r * φ (1:R)) = _
  rw [map_one, mul_one]

def leftIndRegularInvLinear (φ : R →ₐ[k] S) : S →ₗ[S]
    BalancedTensor.T (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R))) :=
  (LinearMap.toSpanSingleton S _) (BalancedTensor.mk
    (show AlgebraInduction.Bimod φ from (1:S)) (show Obj (regular (k := k) (R := R)) from (1:R)))

lemma leftIndRegularInvLinear_apply (φ : R →ₐ[k] S) (s : S) :
    leftIndRegularInvLinear φ s = BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj (regular (k := k) (R := R)))
      (show AlgebraInduction.Bimod φ from s) (1:R) := by
  exact (AlgebraInduction.mk_one_smul φ
    (ModuleCat.of R (Obj (regular (k := k) (R := R)))) s (1:R)).symm

lemma leftIndRegularInvLinear_right (φ : R →ₐ[k] S) (r : Rᵐᵒᵖ) (s : S) :
    leftIndRegularInvLinear φ (s * φ r.unop) = r • leftIndRegularInvLinear φ s := by
  rw [leftIndRegularInvLinear_apply, leftIndRegularInvLinear_apply]
  trans BalancedTensor.mk (k := k) (R := R) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R)))
    (r • (show AlgebraInduction.Bimod φ from s)) (1:R)
  · rfl
  trans BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (r.unop • (show Obj (regular (k := k) (R := R)) from (1:R)))
  · exact BalancedTensor.balance _ _ _
  change BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (r.unop * (1 * 1)) =
    BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (1 * (1 * r.unop))
  exact congrArg (fun z : R => BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R))) (show AlgebraInduction.Bimod φ from s)
    (show Obj (regular (k := k) (R := R)) from z)) (show r.unop * ((1:R)*1) = (1:R)*(1*r.unop) by simp only [one_mul, mul_one])

def leftIndRegularInv (φ : R →ₐ[k] S) :
    rightRestrictedRegular φ ⟶ leftIndObj φ (regular (k := k) (R := R)) :=
  ofBimoduleHom
    (show AlgebraInduction.Bimod φ →ₗ[S] _ from leftIndRegularInvLinear φ)
    (leftIndRegularInvLinear_right φ)

def leftIndRegularIso (φ : R →ₐ[k] S) :
    leftIndObj φ (regular (k := k) (R := R)) ≅ rightRestrictedRegular φ where
  hom := leftIndRegularHom φ
  inv := leftIndRegularInv φ
  hom_inv_id := by
    apply leftInd_hom_ext φ
    intro s r
    change leftIndRegularInvLinear φ (show S from leftIndRegularHom φ
      (show leftIndObj φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)) =
      BalancedTensor.mk s r
    trans leftIndRegularInvLinear φ ((show S from s) * φ r)
    · exact congrArg (leftIndRegularInvLinear φ) (leftIndRegularHom_mk φ s r)
    rw [leftIndRegularInvLinear_apply]
    trans BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R)))
      (MulOpposite.op (show R from r) • s) (1:R)
    · rfl
    trans BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj (regular (k := k) (R := R))) s
      ((show R from r) • (show Obj (regular (k := k) (R := R)) from (1:R)))
    · exact BalancedTensor.balance _ _ _
    change BalancedTensor.mk s (show Obj (regular (k := k) (R := R)) from ((show R from r) * (1*1) : R)) =
      BalancedTensor.mk s r
    exact congrArg (fun z : R => BalancedTensor.mk s
      (show Obj (regular (k := k) (R := R)) from z)) (by exact (congrArg (fun z : R => (show R from r)*z) (one_mul (1:R))).trans (mul_one (show R from r)))
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (show S from leftIndRegularHom φ (leftIndRegularInvLinear φ (show S from s))) =
      (show S from s)
    trans (show S from leftIndRegularHom φ (BalancedTensor.mk
      (show AlgebraInduction.Bimod φ from s) (show Obj (regular (k := k) (R := R)) from (1:R))))
    · exact congrArg (fun x => (show S from leftIndRegularHom φ x)) (leftIndRegularInvLinear_apply φ s)
    exact (leftIndRegularHom_mk φ _ _).trans
      (show (show S from s) * φ (1:R) = (show S from s) by rw [map_one, mul_one])

def rightRestrictedRegularIso (φ : R →ₐ[k] S) :
    (rightFunctor (k := k) (R := S) (S := R)).obj (rightRestrictedRegular φ) ≅
      (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ) :=
by
  let X := (rightFunctor (k := k) (R := S) (S := R)).obj (rightRestrictedRegular φ)
  let Z := (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z)
    (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := fun x : X =>
        (show (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ) from MulOpposite.op (show S from x))
      invFun := fun x => (show Sᵐᵒᵖ from x).unop
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change MulOpposite.op ((1:S) * ((show S from x) * φ r.unop)) =
          MulOpposite.op ((show S from x) * φ r.unop)
        rw [one_mul] }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma leftInducedResolution_finite (φ : R →ₐ[k] S) (n : ℕ) :
    Module.Finite (Alg k S R) ((leftInducedResolution φ).complex.X n) := by
  change Module.Finite (Alg k S R)
    ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  exact Module.Finite.of_restrictScalars_finite k _ _

def leftInducedRightResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) :=
  Tachikawa.transportResolution
    (rightResolutionOf (leftInducedResolution φ) (leftInducedResolution_finite φ))
    ((rightFunctor (k := k) (R := S) (S := R)).mapIso
      ((leftIndComparisonIso φ (regular (k := k) (R := R))) ≪≫ leftIndRegularIso φ) ≪≫
      rightRestrictedRegularIso φ)

def inducedRightFactorIso (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (leftEnvelopingMap (U := R) φ) ⋙
      AlgebraInduction.functor (rightEnvelopingMap (U := S) φ) ≅
      AlgebraInduction.functor (envelopingMap φ) :=
  AlgebraInduction.compositionIso _ _ ≪≫ eqToIso (by
    congr 1
    ext a <;> rfl)

def inducedRightComplexIso (φ : R →ₐ[k] S) :
    rightComplex (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ.op).mapHomologicalComplex _).obj
        (leftInducedRightResolution φ).complex := by
  let P := (regularResolution (k := k) (R := R)).complex
  let J := AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)
  let L := AlgebraInduction.functor (rightEnvelopingMap (U := S) φ)
  let U := rightFunctor (k := k) (R := S) (S := S)
  let V := rightFunctor (k := k) (R := S) (S := R)
  let I := AlgebraInduction.functor φ.op
  let a : L ⋙ U ≅ V ⋙ I :=
    Functor.isoWhiskerRight (rightIndComparison (U := S) φ) U ≪≫
      rightIndUnderlyingComparison (U := S) φ
  let b := Functor.isoWhiskerRight (inducedRightFactorIso φ) U
  exact (NatIso.mapHomologicalComplex b _).symm.app P ≪≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft J a) _).app P

def inducedRightHomotopy (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))) :
    HomotopyEquiv (rightComplex (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ.op).mapHomologicalComplex _).obj Q.complex) :=
  (HomotopyEquiv.ofIso (inducedRightComplexIso φ)).trans
    ((AlgebraInduction.functor φ.op).mapHomotopyEquiv
      (ProjectiveResolution.homotopyEquiv (leftInducedRightResolution φ) Q))

lemma inducedCoker_right_projective (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)))
    (n : ℕ) (hn : CategoryTheory.Limits.IsZero (Q.complex.X (n+1))) :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) n))) := by
  let I := AlgebraInduction.functor φ.op
  let C := (I.mapHomologicalComplex _).obj Q.complex
  have hC : CategoryTheory.Limits.IsZero (C.X (n+1)) := I.map_isZero hn
  let : Subsingleton (C.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hC
  exact coker_right_projective_of_homotopy (inducedRegularComplex φ) C n (inducedRightHomotopy φ Q)

end Tachikawa.Enveloping

end
end OAI
