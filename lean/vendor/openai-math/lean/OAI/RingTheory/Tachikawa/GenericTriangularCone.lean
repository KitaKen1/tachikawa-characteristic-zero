import OAI.RingTheory.Tachikawa.GenericTriangular
import OAI.RingTheory.Tachikawa.GenericCompleteCone

/-! Characteristic-independent excerpts from pinned OpenAI Math Cone.lean,
Apache-2.0. Generic declarations are unchanged. The cone abbreviation is
placed in a Field/Ring/Algebra wrapper without the unused CharP 2 assumption;
no DownCone or characteristic-two boundary theorem is imported. -/
namespace OAI
noncomputable section
namespace Tachikawa.Triangular
open CategoryTheory
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  {P : ChainComplex (ModuleCat.{0} R) ℤ} (u : P ⟶ Enveloping.tensorComplex F P)
abbrev cone := CompleteCone.complex (crossMap F u)
end Tachikawa.Triangular

namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
abbrev oneFree := freeObj (R := R) (PUnit : Type)
instance : Module.Finite R (oneFree (R := R)) := inferInstanceAs (Module.Finite R (PUnit → R))
instance : Module.Projective R (oneFree (R := R)) := inferInstanceAs (Module.Projective R (PUnit → R))
def regIn₀ : D₀Obj F (oneFree (R := R)) →ₗ[Alg F] Alg F :=
  (LinearMap.proj PUnit.unit).comp (D₀FreeInclusion F PUnit)
def regIn₁ : D₁Obj F (oneFree (R := R)) →ₗ[Alg F] Alg F :=
  (LinearMap.proj PUnit.unit).comp (D₁FreeInclusion F PUnit)
def regOut₀ : Alg F →ₗ[Alg F] D₀Obj F (oneFree (R := R)) :=
  (D₀FreeProjection F PUnit).comp (LinearMap.pi fun _ => LinearMap.id)
def regOut₁ : Alg F →ₗ[Alg F] D₁Obj F (oneFree (R := R)) :=
  (D₁FreeProjection F PUnit).comp (LinearMap.pi fun _ => LinearMap.id)
lemma reg_split : (regIn₀ F).comp (regOut₀ F) + (regIn₁ F).comp (regOut₁ F) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply TrivSqZeroExt.ext
  · apply Prod.ext
    · change upper F a + 0 = a.fst.1
      exact add_zero _
    · change 0 + lower F a = a.fst.2
      exact zero_add _
  · change freeTensorEval F PUnit (freeTensorInv F PUnit (fun _ => off F a)) PUnit.unit + 0 = a.snd
    rw [freeTensorEval_inv,add_zero]
    rfl

variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]
include hP in
lemma D₀_totallyAcyclic : TotallyAcyclic (D₀Complex F P) := by
  refine ⟨fun j => D₀Map_exact F _ _ (hP.1 j),?_⟩
  intro j f hf
  let f₀ : D₀Obj F (P.X j) ⟶ D₀Obj F (oneFree (R := R)) := ModuleCat.ofHom ((regOut₀ F).comp f)
  have hf₀ : D₀Map F (P.d (j+1) j) ≫ f₀ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₀ F).comp f).comp ((D₀Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  obtain ⟨g₀,hg₀⟩ := D₀_boundaries F P hP (oneFree (R := R)) j f₀ hf₀
  have hf₁ : (regOut₁ F).comp f = 0 :=
    ModuleCat.hom_ext_iff.mp (cross₀₁_zero (ModuleCat.ofHom ((regOut₁ F).comp f)))
  refine ⟨(regIn₀ F).comp g₀.hom,?_⟩
  have hg := ModuleCat.hom_ext_iff.mp hg₀
  change g₀.hom.comp ((D₀Complex F P).d j (j-1)).hom = (regOut₀ F).comp f at hg
  erw [LinearMap.comp_assoc,hg]
  have hs := congrArg (fun p : Alg F →ₗ[Alg F] Alg F => p.comp f) (reg_split F)
  rw [LinearMap.add_comp,LinearMap.comp_assoc,LinearMap.comp_assoc,hf₁,
    LinearMap.comp_zero,add_zero,LinearMap.id_comp] at hs
  exact hs

variable [FiniteDimensional k (Enveloping.Obj F)] [Module.Projective R (Enveloping.Obj F)]
include hP in
omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma D₁_totallyAcyclic : TotallyAcyclic (D₁Complex F P) := by
  let N := oneFree (R := R)
  let : Module.Finite R N := inferInstanceAs (Module.Finite R (PUnit → R))
  let : Module.Projective R N := inferInstanceAs (Module.Projective R (PUnit → R))
  let : Module.Finite R (tensorObj F N) := by
    let : Module.Finite R (Enveloping.Obj F) := Module.Finite.of_restrictScalars_finite k _ _
    exact Module.Finite.equiv (freeTensorEquiv F PUnit).symm
  let : Module.Projective R (tensorObj F N) :=
    BalancedTensor.map_projective (k := k) (R := R) (S := R) (M := Enveloping.Obj F) (N := N)
  refine ⟨fun j => D₁Map_exact F _ _ (hP.1 j),?_⟩
  intro j f hf
  let f₀ : D₁Obj F (P.X j) ⟶ D₀Obj F N := ModuleCat.ofHom ((regOut₀ F).comp f)
  let f₁ : D₁Obj F (P.X j) ⟶ D₁Obj F N := ModuleCat.ofHom ((regOut₁ F).comp f)
  have hf₀ : D₁Map F (P.d (j+1) j) ≫ f₀ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₀ F).comp f).comp ((D₁Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  have hf₁ : D₁Map F (P.d (j+1) j) ≫ f₁ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₁ F).comp f).comp ((D₁Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  obtain ⟨g₀,hg₀⟩ := cross_boundaries F P hP N j f₀ hf₀
  obtain ⟨g₁,hg₁⟩ := D₁_boundaries F P hP N j f₁ hf₁
  refine ⟨(regIn₀ F).comp g₀.hom + (regIn₁ F).comp g₁.hom,?_⟩
  have hg₀ := ModuleCat.hom_ext_iff.mp hg₀
  have hg₁ := ModuleCat.hom_ext_iff.mp hg₁
  change g₀.hom.comp ((D₁Complex F P).d j (j-1)).hom = (regOut₀ F).comp f at hg₀
  change g₁.hom.comp ((D₁Complex F P).d j (j-1)).hom = (regOut₁ F).comp f at hg₁
  change (regIn₀ F).comp (g₀.hom.comp ((D₁Complex F P).d j (j-1)).hom) +
    (regIn₁ F).comp (g₁.hom.comp ((D₁Complex F P).d j (j-1)).hom) = f
  rw [hg₀,hg₁]
  exact congrArg (fun p : Alg F →ₗ[Alg F] Alg F => p.comp f) (reg_split F)

end Tachikawa.Triangular

namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  [FiniteDimensional k R] [FiniteDimensional k F]
  [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]
  {P : ChainComplex (ModuleCat.{0} R) ℤ} (u : P ⟶ Enveloping.tensorComplex F P)
  (hP : TotallyAcyclic P) (fP : ∀ j, Module.Finite R (P.X j))
  (pP : ∀ j, Module.Projective R (P.X j))
include hP in
omit [FiniteDimensional k R] in
lemma cone_totallyAcyclic : TotallyAcyclic (cone F u) := by
  let : FiniteDimensional k (Enveloping.Obj F) := inferInstanceAs (FiniteDimensional k F)
  let : Module.Finite Rᵐᵒᵖ (Enveloping.Obj F) := Module.Finite.of_restrictScalars_finite k _ _
  exact CompleteCone.totallyAcyclic _ (D₀_totallyAcyclic F P hP) (D₁_totallyAcyclic F P hP)
include fP in
omit [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma cone_finite (j : ℤ) : Module.Finite (Alg F) ((cone F u).X j) := by
  apply CompleteCone.finite
  · intro i
    let := fP i
    let : FiniteDimensional k (P.X i) := Module.Finite.trans R _
    change Module.Finite (Alg F) (D₀Obj F (P.X i))
    exact Module.Finite.of_restrictScalars_finite k _ _
  · intro i
    let := fP i
    let : FiniteDimensional k (P.X i) := Module.Finite.trans R _
    change Module.Finite (Alg F) (D₁Obj F (P.X i))
    exact Module.Finite.of_restrictScalars_finite k _ _
include fP pP in
omit [FiniteDimensional k R] [FiniteDimensional k F]
  [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma cone_projective (j : ℤ) : Module.Projective (Alg F) ((cone F u).X j) := by
  apply CompleteCone.projective
  · intro i
    let := fP i
    let := pP i
    exact D₀_projective F (P.X i)
  · intro i
    let := fP i
    let := pP i
    exact D₁_projective F (P.X i)
end Tachikawa.Triangular

end
end OAI
