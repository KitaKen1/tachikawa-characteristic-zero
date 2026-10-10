import OAI.RingTheory.Tachikawa.RestrictedRegular
import OAI.RingTheory.Tachikawa.PerfectCutoff

/-! Characteristic-independent excerpts from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def restrictedRegularMap (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (envelopingMap φ)).obj (regular (k := k) (R := S)) :=
  homOfLinear
    ((AlgebraInduction.resUnderlyingEquiv (envelopingMap φ) (regular (k := k) (R := S))).symm.toLinearMap.comp
      (regularUnderlyingEquiv.symm.toLinearMap.comp
        (φ.toLinearMap.comp regularUnderlyingEquiv.toLinearMap))) (by
    intro r s x
    change φ (r * ((show R from x) * s.unop)) =
      φ r * (φ (show R from x) * φ s.unop)
    exact (φ.map_mul r ((show R from x) * s.unop)).trans
      (congrArg (fun z : S => φ r * z) (φ.map_mul (show R from x) s.unop)))

lemma restrictedRegularMap_apply (φ : R →ₐ[k] S) (x : R) :
    regularUnderlyingEquiv ((AlgebraInduction.resUnderlyingEquiv (envelopingMap φ)
      (regular (k := k) (R := S))) (restrictedRegularMap φ (regularUnderlyingEquiv.symm x))) = φ x := rfl

end Tachikawa.Enveloping



namespace Tachikawa.AlgebraInduction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)
variable {ι : Type} (c : ComplexShape ι)

abbrev complexInduction := (functor φ).mapHomologicalComplex c
abbrev complexRestriction := (res φ).mapHomologicalComplex c

def complexUnit (P : HomologicalComplex (ModuleCat.{0} R) c) :
    P ⟶ (complexRestriction φ c).obj ((complexInduction φ c).obj P) where
  f i := unit φ (P.X i)
  comm' i j _ := (unit_naturality φ (P.d i j)).symm

def complexExtend {P : HomologicalComplex (ModuleCat.{0} R) c}
    {Q : HomologicalComplex (ModuleCat.{0} S) c}
    (f : P ⟶ (complexRestriction φ c).obj Q) :
    (complexInduction φ c).obj P ⟶ Q where
  f i := extend φ (f.f i)
  comm' i j _ := by
    apply (homEquiv φ (P.X i) (Q.X j)).injective
    change unit φ (P.X i) ≫ (res φ).map (extend φ (f.f i) ≫ Q.d i j) =
      unit φ (P.X i) ≫ (res φ).map ((functor φ).map (P.d i j) ≫ extend φ (f.f j))
    rw [Functor.map_comp,Functor.map_comp,← Category.assoc,unit_extend,
      ← Category.assoc,← unit_naturality,Category.assoc,unit_extend]
    exact f.comm i j

lemma complexUnit_extend {P : HomologicalComplex (ModuleCat.{0} R) c}
    {Q : HomologicalComplex (ModuleCat.{0} S) c}
    (f : P ⟶ (complexRestriction φ c).obj Q) :
    complexUnit φ c P ≫ (complexRestriction φ c).map (complexExtend φ c f) = f := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact unit_extend φ (f.f i)

end Tachikawa.AlgebraInduction



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)

abbrev inducedRegularCochain : CochainComplex (ModuleCat.{0} (Alg k S S)) ℤ :=
  (AlgebraInduction.complexInduction (envelopingMap φ) (.up ℤ)).obj
    (regularResolution (k := k) (R := R)).cochainComplex

def regularPreAugmentation : (regularResolution (k := k) (R := R)).cochainComplex ⟶
    (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj (regular (k := k) (R := S))) :=
  (regularResolution (k := k) (R := R)).π' ≫
    (CochainComplex.singleFunctor _ 0).map (restrictedRegularMap φ) ≫
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).inv.app _

def inducedRegularAugmentation : inducedRegularCochain φ ⟶
    (CochainComplex.singleFunctor _ 0).obj (regular (k := k) (R := S)) :=
  AlgebraInduction.complexExtend (envelopingMap φ) (.up ℤ) (regularPreAugmentation φ)

lemma induced_regular_square {U : ModuleCat.{0} (Alg k S S)} {N : ModuleCat.{0} (Alg k R R)}
    (v : regular (k := k) (R := S) ⟶ U)
    (b : (AlgebraInduction.res (envelopingMap φ)).obj U ⟶ N) :
    AlgebraInduction.complexUnit (envelopingMap φ) (.up ℤ)
      (regularResolution (k := k) (R := R)).cochainComplex ≫
    (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
      (inducedRegularAugmentation φ ≫ (CochainComplex.singleFunctor _ 0).map v) ≫
    (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U ≫
    (CochainComplex.singleFunctor _ 0).map b =
    (regularResolution (k := k) (R := R)).π' ≫
      (CochainComplex.singleFunctor _ 0).map
        (restrictedRegularMap φ ≫ (AlgebraInduction.res (envelopingMap φ)).map v ≫ b) := by
  rw [Functor.map_comp]
  rw [← Category.assoc,← Category.assoc,← Category.assoc]
  dsimp only [inducedRegularAugmentation]
  rw [AlgebraInduction.complexUnit_extend]
  dsimp only [regularPreAugmentation]
  simp only [Category.assoc]
  have hn : (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
      ((CochainComplex.singleFunctor _ 0).map v) ≫
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U =
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map ((AlgebraInduction.res (envelopingMap φ)).map v) :=
    (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.naturality v
  rw [← Category.assoc ((AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
    ((CochainComplex.singleFunctor _ 0).map v)), hn]
  simp only [Iso.inv_hom_id_app_assoc,Functor.map_comp,Category.assoc]

end Tachikawa.Enveloping

namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

lemma kProjective_chain_representative (K L : CochainComplex C ℤ) [K.IsKProjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b,hb⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).surjective
      ((e.app K).hom ≫ a ≫ (e.app L).inv)
  obtain ⟨f,rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨f,?_⟩
  have ht := congrArg (fun t => (e.app K).inv ≫ t ≫ (e.app L).hom) hb
  change e.inv.app K ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L =
    e.inv.app K ≫ (e.hom.app K ≫ a ≫ e.inv.app L) ≫ e.hom.app L at ht
  simpa [e] using ht

end Tachikawa

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R] {M : ModuleCat.{0} R}

lemma finite_resolution_cochain (P : ProjectiveResolution M)
    (hfin : ∀ n, Module.Finite R (P.complex.X n)) (i : ℤ) :
    Module.Finite R (P.cochainComplex.X i) := by
  by_cases hi : i ≤ 0
  · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
    let := hfin n
    exact Module.Finite.equiv (P.cochainComplexXIso (-(n:ℤ)) n).toLinearEquiv.symm
  · let := ModuleCat.isZero_iff_subsingleton.mp
      (P.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega))
    infer_instance

namespace Enveloping
open scoped TensorProduct
variable {k S : Type} [Field k] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S] (φ : R →ₐ[k] S)

instance inducedRegularCochain_finite (i : ℤ) :
    Module.Finite (Alg k S S) ((inducedRegularCochain φ).X i) := by
  let P := regularResolution (k := k) (R := R)
  let : Module.Finite (Alg k R R) (P.cochainComplex.X i) :=
    finite_resolution_cochain P (fun _ => inferInstance) i
  let : FiniteDimensional k (P.cochainComplex.X i) := Module.Finite.trans (Alg k R R) _
  let : FiniteDimensional k ((AlgebraInduction.functor (envelopingMap φ)).obj
    (P.cochainComplex.X i)) := inferInstance
  change Module.Finite (Alg k S S) ((AlgebraInduction.functor (envelopingMap φ)).obj
    (P.cochainComplex.X i))
  exact Module.Finite.of_restrictScalars_finite k _ _

instance inducedRegularCochain_projective (i : ℤ) :
    Projective ((inducedRegularCochain φ).X i) := by
  let P := regularResolution (k := k) (R := R)
  let : Module.Finite (Alg k R R) (P.cochainComplex.X i) :=
    finite_resolution_cochain P (fun _ => inferInstance) i
  change Projective ((AlgebraInduction.functor (envelopingMap φ)).obj (P.cochainComplex.X i))
  infer_instance

instance inducedRegularCochain_bounded : (inducedRegularCochain φ).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (AlgebraInduction.functor (envelopingMap φ)).map_isZero
    ((regularResolution (k := k) (R := R)).cochainComplex.isZero_of_isStrictlyLE 0 i hi)

instance inducedRegularCochain_isKProjective : (inducedRegularCochain φ).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

end Enveloping
end Tachikawa

end
end OAI
