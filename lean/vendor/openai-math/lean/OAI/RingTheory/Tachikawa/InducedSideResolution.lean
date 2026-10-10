import OAI.RingTheory.Tachikawa.OneSidedInduction

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma leftFunctor_eq : leftFunctor (k := k) (R := R) (S := S) =
    ModuleCat.restrictScalars (Algebra.TensorProduct.includeLeft : R →ₐ[k] Alg k R S).toRingHom := rfl
lemma rightFunctor_eq : rightFunctor (k := k) (R := R) (S := S) =
    ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] Alg k R S).toRingHom := rfl

lemma leftFunctor_map_exact (T : ShortComplex (ModuleCat (Alg k R S))) (h : T.Exact) :
    (T.map (leftFunctor (k := k) (R := R) (S := S))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h
lemma rightFunctor_map_exact (T : ShortComplex (ModuleCat (Alg k R S))) (h : T.Exact) :
    (T.map (rightFunctor (k := k) (R := R) (S := S))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance : PreservesFiniteLimits (leftFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (leftFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (leftFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.1
instance : PreservesFiniteColimits (leftFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (leftFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (leftFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.2
instance : PreservesFiniteLimits (rightFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (rightFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (rightFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.1
instance : PreservesFiniteColimits (rightFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (rightFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (rightFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.2

end Tachikawa.Enveloping

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftResolutionOf {M : ModuleCat (Alg k R S)} (P : CategoryTheory.ProjectiveResolution M)
    (hP : ∀ n, Module.Finite (Alg k R S) (P.complex.X n)) :
    CategoryTheory.ProjectiveResolution (leftFunctor.obj M) where
  complex := (leftFunctor.mapHomologicalComplex _).obj P.complex
  projective n := by
    let := hP n
    let : Module.Projective R (Obj (P.complex.X n)) := projective_left _
    change Projective (ModuleCat.of R (Obj (P.complex.X n)))
    infer_instance
  π := (leftFunctor.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

def rightResolutionOf {M : ModuleCat (Alg k R S)} (P : CategoryTheory.ProjectiveResolution M)
    (hP : ∀ n, Module.Finite (Alg k R S) (P.complex.X n)) :
    CategoryTheory.ProjectiveResolution (rightFunctor.obj M) where
  complex := (rightFunctor.mapHomologicalComplex _).obj P.complex
  projective n := by
    let := hP n
    let : Module.Projective Sᵐᵒᵖ (Obj (P.complex.X n)) := projective_right _
    change Projective (ModuleCat.of Sᵐᵒᵖ (Obj (P.complex.X n)))
    infer_instance
  π := (rightFunctor.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] {M : C} [Projective M]

lemma map_resolution_quasiIso (P : ProjectiveResolution M) :
    QuasiIso ((F.mapHomologicalComplex _).map P.π) := by
  let e := ProjectiveResolution.homotopyEquiv P (ProjectiveResolution.self M)
  have h : e.hom = P.π := by
    simpa only [e, ProjectiveResolution.self, Category.comp_id] using
      ProjectiveResolution.homotopyEquiv_hom_π P (ProjectiveResolution.self M)
  rw [← h]
  exact (F.mapHomotopyEquiv e).quasiIso_hom

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] {ι : Type*} {c : ComplexShape ι}

lemma quasiIso_map_natIso (e : F ≅ G) {K L : HomologicalComplex C c} (f : K ⟶ L) :
    QuasiIso ((F.mapHomologicalComplex c).map f) ↔ QuasiIso ((G.mapHomologicalComplex c).map f) := by
  let i := NatIso.mapHomologicalComplex e c
  have h := i.hom.naturality f
  rw [← quasiIso_iff_comp_right ((F.mapHomologicalComplex c).map f) (i.hom.app L), h,
    quasiIso_iff_comp_left (i.hom.app K)]

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

instance regular_right_projective : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := by
  let : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_equiv (regularRightEquiv (k := k) (R := R)).symm

instance regular_left_projective : Module.Projective R (Obj (regular (k := k) (R := R))) :=
  Module.Projective.of_equiv (regularLeftEquiv (k := k) (R := R)).symm

instance rightFunctor_reflectsIsomorphisms :
    (rightFunctor (k := k) (R := R) (S := S)).ReflectsIsomorphisms := by
  rw [rightFunctor_eq]
  infer_instance

instance leftFunctor_reflectsIsomorphisms :
    (leftFunctor (k := k) (R := R) (S := S)).ReflectsIsomorphisms := by
  rw [leftFunctor_eq]
  infer_instance

omit [FiniteDimensional k S] in
lemma right_induction_regular_quasiIso (φ : R →ₐ[k] S) :
    QuasiIso (((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := rightResolutionOf P (fun n => inferInstance)
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := regular_right_projective
  let : Projective ((rightFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of Rᵐᵒᵖ (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := AlgebraInduction.functor φ.op
  let T := rightFunctor (k := k) (R := R) (S := R)
  let T' := rightFunctor (k := k) (R := R) (S := S)
  let J := AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)
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
  have hB : QuasiIso (((rightIndFunctor (U := R) φ ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (rightIndUnderlyingComparison (U := R) φ) P.π).mpr hI
  have hJ : QuasiIso (((J ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (Functor.isoWhiskerRight (rightIndComparison (U := R) φ) T') P.π).mpr hB
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def rightInducedResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      (regular (k := k) (R := R))) where
  complex := ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  π := ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := by
    let := right_induction_regular_quasiIso φ
    infer_instance

end Tachikawa.Enveloping


end
end OAI
