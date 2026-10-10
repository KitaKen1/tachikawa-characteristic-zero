import OAI.RingTheory.Tachikawa.FiniteOuterReplacement

/-! Characteristic-independent excerpts from OpenAI Math,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def freeEndo : ModuleCat R ⥤ ModuleCat R :=
  AlgebraInduction.res (Algebra.ofId k R) ⋙ AlgebraInduction.functor (Algebra.ofId k R)
instance : (freeEndo (k := k) (R := R)).Additive := inferInstanceAs
  ((AlgebraInduction.res (Algebra.ofId k R) ⋙ AlgebraInduction.functor (Algebra.ofId k R)).Additive)

def freeCounit (M : ModuleCat R) : (freeEndo (k := k)).obj M ⟶ M :=
  AlgebraInduction.extend (Algebra.ofId k R) (𝟙 _)

lemma freeCounit_surjective (M : ModuleCat R) : Function.Surjective (freeCounit (k := k) M) := by
  intro x
  refine ⟨BalancedTensor.mk (k := k) (R := k) (S := R)
    (show AlgebraInduction.Bimod (Algebra.ofId k R) from (1 : R))
    (show (AlgebraInduction.res (Algebra.ofId k R)).obj M from x), ?_⟩
  change (1 : R) • x = x
  exact one_smul R x

instance (M : ModuleCat R) : Epi (freeCounit (k := k) M) :=
  (ModuleCat.epi_iff_surjective _).2 (freeCounit_surjective M)

def freeCounitNat : freeEndo (k := k) (R := R) ⟶ 𝟭 _ where
  app := freeCounit
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro r x
    change (show R from r) • f (show M from x) = f ((show R from r) • (show M from x))
    exact (f.hom.map_smul _ _).symm

instance : Epi (freeCounitNat (k := k) (R := R)) := by
  let (M : ModuleCat R) : Epi ((freeCounitNat (k := k)).app M) := inferInstanceAs (Epi (freeCounit (k := k) M))
  exact NatTrans.epi_of_epi_app _

def freeKernel : ModuleCat R ⥤ ModuleCat R := kernel (freeCounitNat (k := k) (R := R))
instance : (freeKernel (k := k) (R := R)).Additive := by
  constructor
  intro X Y f g
  dsimp only [freeKernel]
  let ι := kernel.ι (freeCounitNat (k := k) (R := R))
  let : Mono (ι.app Y) := inferInstance
  apply (cancel_mono (ι.app Y)).1
  erw [ι.naturality,Functor.map_add,Preadditive.comp_add,
    Preadditive.add_comp,ι.naturality,ι.naturality]

def freeι (M : ModuleCat R) : (freeKernel (k := k)).obj M ⟶ (freeEndo (k := k)).obj M :=
  (kernel.ι (freeCounitNat (k := k))).app M

lemma freeι_counit (M : ModuleCat R) : freeι (k := k) M ≫ freeCounit M = 0 :=
  congrArg (fun f => f.app M) (kernel.condition (freeCounitNat (k := k)))

def freeShort (M : ModuleCat R) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (freeι (k := k) M) (freeCounit M) (freeι_counit M)

lemma freeShort_exact (M : ModuleCat R) : (freeShort (k := k) M).ShortExact := by
  let T : ShortComplex (ModuleCat R ⥤ ModuleCat R) :=
    ShortComplex.mk (kernel.ι (freeCounitNat (k := k))) freeCounitNat (kernel.condition _)
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel _ }
  exact hT.map ((evaluation _ _).obj M)

instance freeEndo_projective (M : ModuleCat R) [FiniteDimensional k M] :
    Projective ((freeEndo (k := k)).obj M) := by
  let : Module.Finite k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) :=
    inferInstanceAs (Module.Finite k M)
  let : Module.Projective k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) := inferInstance
  change Projective ((AlgebraInduction.functor (Algebra.ofId k R)).obj _)
  infer_instance

variable [FiniteDimensional k R]
instance freeEndo_finite (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((freeEndo (k := k)).obj M) := by
  let : FiniteDimensional k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) :=
    inferInstanceAs (FiniteDimensional k M)
  change FiniteDimensional k ((AlgebraInduction.functor (Algebra.ofId k R)).obj _)
  infer_instance

instance freeKernel_finite (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((freeKernel (k := k)).obj M) := by
  have : Mono (freeι (k := k) M) := inferInstanceAs
    (Mono ((kernel.ι (freeCounitNat (k := k))).app M))
  have hi : Function.Injective (freeι (k := k) M) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact Module.Finite.of_injective ((freeι M).hom.restrictScalars k) hi

omit [FiniteDimensional k R] in
lemma freeKernel_pd (M : ModuleCat R) [FiniteDimensional k M] (n : ℕ)
    [HasProjectiveDimensionLE M (n+1)] :
    HasProjectiveDimensionLE ((freeKernel (k := k)).obj M) n := by
  apply (freeShort_exact (k := k) M).hasProjectiveDimensionLT_X₁ (n+1)
  · change HasProjectiveDimensionLT ((freeEndo (k := k)).obj M) (n+1)
    exact hasProjectiveDimensionLT_of_ge _ 1 (n+1) (by omega)
  · exact inferInstanceAs (HasProjectiveDimensionLE M (n+1))

end Tachikawa






namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev freeComplex (P : CochainComplex (ModuleCat R) ℤ) :=
  ((freeEndo (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
abbrev kernelComplex (P : CochainComplex (ModuleCat R) ℤ) :=
  ((freeKernel (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

def freeComplexCounit (P : CochainComplex (ModuleCat R) ℤ) : freeComplex (k := k) P ⟶ P where
  f i := freeCounit (P.X i)
  comm' i j _ := ((freeCounitNat (k := k)).naturality (P.d i j)).symm

def freeComplexι (P : CochainComplex (ModuleCat R) ℤ) : kernelComplex (k := k) P ⟶ freeComplex (k := k) P where
  f i := freeι (P.X i)
  comm' i j _ := ((kernel.ι (freeCounitNat (k := k))).naturality (P.d i j)).symm

def freeComplexShort (P : CochainComplex (ModuleCat R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (freeComplexι (k := k) P) (freeComplexCounit (k := k) P) (by
    apply HomologicalComplex.Hom.ext
    funext i
    exact freeι_counit (P.X i))

lemma freeComplexShort_exact (P : CochainComplex (ModuleCat R) ℤ) :
    (freeComplexShort (k := k) P).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact freeShort_exact (P.X i)

end Tachikawa





namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def shortExactReplacementMapDual (S : ShortComplex (CochainComplex C ℤ))
    {Q : CochainComplex C ℤ} (α : Q ⟶ S.X₁) : mappingCone (α ≫ S.f) ⟶ S.X₃ :=
  mappingCone.map (α ≫ S.f) S.f α (𝟙 S.X₂) (by simp) ≫ mappingCone.descShortComplex S

lemma shortExactReplacementMapDual_quasiIso (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) {Q : CochainComplex C ℤ} (α : Q ⟶ S.X₁) [QuasiIso α] :
    QuasiIso (shortExactReplacementMapDual S α) := by
  have := mappingCone_map_quasiIso (α ≫ S.f) S.f α (𝟙 S.X₂) (by simp)
  have := mappingCone.quasiIso_descShortComplex hS
  exact quasiIso_comp _ _

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

structure IndReplacement (P : CochainComplex (ModuleCat.{0} R) ℤ) where
  complex : CochainComplex (ModuleCat.{0} R) ℤ
  map : complex ⟶ P
  quasiIso : QuasiIso map
attribute [instance] IndReplacement.quasiIso

def indReplacement : (n : ℕ) → (P : CochainComplex (ModuleCat.{0} R) ℤ) → IndReplacement P
  | 0, P => ⟨P,𝟙 P,inferInstance⟩
  | n+1, P =>
    let t := indReplacement n (kernelComplex (k := k) P)
    { complex := mappingCone (t.map ≫ freeComplexι P)
      map := shortExactReplacementMapDual (freeComplexShort P) t.map
      quasiIso := by
        exact @shortExactReplacementMapDual_quasiIso _ _ _ (freeComplexShort P)
          (freeComplexShort_exact P) _ t.map t.quasiIso }

lemma mappingCone_projective {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L)
    (hK : ∀ i, Projective (K.X i)) (hL : ∀ i, Projective (L.X i)) (i : ℤ) :
    Projective ((mappingCone f).X i) := by
  let := hK (i+1)
  let := hL i
  exact Projective.of_iso (homotopyCofiber.XIsoBiprod f i (i+1) (by rfl)).symm inferInstance

lemma mappingCone_finite {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L)
    (hK : ∀ i, FiniteDimensional k (K.X i)) (hL : ∀ i, FiniteDimensional k (L.X i)) (i : ℤ) :
    FiniteDimensional k ((mappingCone f).X i) := by
  let := hK (i+1)
  let := hL i
  let e := homotopyCofiber.XIsoBiprod f i (i+1) (by rfl) ≪≫ ModuleCat.biprodIsoProd _ _
  exact Module.Finite.equiv (e.toLinearEquiv.restrictScalars k).symm

lemma mappingCone_isZero_X {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L) (i : ℤ)
    (hK : IsZero (K.X (i+1))) (hL : IsZero (L.X i)) : IsZero ((mappingCone f).X i) :=
  IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hK,hL⟩)
    (homotopyCofiber.XIsoBiprod f i (i+1) (by rfl))

lemma indReplacement_bounded (n : ℕ) (P : CochainComplex (ModuleCat.{0} R) ℤ) (l u : ℤ)
    (hP : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∀ i, i < l - n ∨ u < i → IsZero ((indReplacement (k := k) n P).complex.X i) := by
  induction n generalizing P with
  | zero => simpa only [indReplacement,Nat.cast_zero,sub_zero] using hP
  | succ n ih =>
    intro i hi
    apply mappingCone_isZero_X
    · apply ih (kernelComplex P)
      · intro j hj
        exact (freeKernel (k := k)).map_isZero (hP j hj)
      · omega
    · exact (freeEndo (k := k)).map_isZero (hP i (by omega))

variable [FiniteDimensional k R]
lemma indReplacement_terms (n : ℕ) (P : CochainComplex (ModuleCat.{0} R) ℤ)
    (hfin : ∀ i, FiniteDimensional k (P.X i))
    (hpd : ∀ i, HasProjectiveDimensionLE (P.X i) n) :
    (∀ i, Projective ((indReplacement (k := k) n P).complex.X i)) ∧
    (∀ i, FiniteDimensional k ((indReplacement (k := k) n P).complex.X i)) := by
  induction n generalizing P with
  | zero =>
    refine ⟨?_,hfin⟩
    intro i
    exact (projective_iff_hasProjectiveDimensionLE_zero (P.X i)).2 (hpd i)
  | succ n ih =>
    obtain ⟨hp,hf⟩ := ih (kernelComplex (k := k) P)
      (fun i => by let := hfin i; exact freeKernel_finite (k := k) (P.X i))
      (fun i => by let := hfin i; let := hpd i; exact freeKernel_pd (k := k) (P.X i) n)
    exact ⟨mappingCone_projective _ hp
      (fun i => by let := hfin i; exact freeEndo_projective (k := k) (P.X i)),
      mappingCone_finite _ hf
      (fun i => by let := hfin i; exact freeEndo_finite (k := k) (P.X i))⟩

theorem bounded_projective_replacement (P : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℕ)
    (hfin : ∀ i, FiniteDimensional k (P.X i))
    (hpd : ∀ i, HasProjectiveDimensionLE (P.X i) n)
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℤ) (f : Q ⟶ P), QuasiIso f ∧
      (∀ i, Projective (Q.X i)) ∧ (∀ i, FiniteDimensional k (Q.X i)) ∧
      (∀ i, i < l-n ∨ u < i → IsZero (Q.X i)) :=
  ⟨(indReplacement (k := k) n P).complex,(indReplacement (k := k) n P).map,inferInstance,
    (indReplacement_terms n P hfin hpd).1,(indReplacement_terms n P hfin hpd).2,
    indReplacement_bounded n P l u hb⟩

end Tachikawa





end
end OAI
