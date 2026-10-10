import OAI.RingTheory.Tachikawa.AdditiveClosure

/-! Characteristic-independent excerpts from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; source files, exact line ranges and hashes are
recorded in vendor/openai-math/manifest.json. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R M : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [FiniteDimensional k M] [Module.Injective R M]

omit [FiniteDimensional k R] in

lemma finite_injective_retract_dual :
    ∃ (n : ℕ) (i : M →ₗ[R] (Fin n → DualBimodule k R))
      (p : (Fin n → DualBimodule k R) →ₗ[R] M), p.comp i = LinearMap.id := by
  let i := finiteCoinducedEmbedding (k := k) (R := R) (M := M)
  obtain ⟨s,hs⟩ := Module.Injective.extension_property R M M _ i
    finiteCoinducedEmbedding_injective LinearMap.id
  exact ⟨_,i,s,hs⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

lemma finiteInjective_inAdd (M : ModuleCat R) [FiniteDimensional k M] [Injective M] :
    InAdd (Enveloping.dualLeftObj (k := k) (R := R)) M := by
  let : Module.Injective R M := Module.injective_module_of_injective_object R M
  obtain ⟨n,i,p,hp⟩ := finite_injective_retract_dual (k := k) (R := R) (M := M)
  let e := ModuleCat.biproductIsoPi (fun _ : Fin n => Enveloping.dualLeftObj (k := k) (R := R))
  refine ⟨n,⟨{i := ModuleCat.ofHom i ≫ e.inv, r := e.hom ≫ ModuleCat.ofHom p, retract := ?_}⟩⟩
  erw [Category.assoc,← Category.assoc e.inv,e.inv_hom_id,Category.id_comp]
  exact ModuleCat.hom_ext hp

end Tachikawa


namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [FiniteDimensional k R]

instance rightFree_preservesFiniteColimits : PreservesFiniteColimits (rightFreeFunctor (k := k) (R := R) (S := S)) :=
  inferInstanceAs (PreservesFiniteColimits ((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))))
instance rightFree_preservesFiniteLimits : PreservesFiniteLimits (rightFreeFunctor (k := k) (R := R) (S := S)) :=
  inferInstanceAs (PreservesFiniteLimits ((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))))

def coindCokerTensorIso (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.C (k := k)).obj M) ≅
      (coindCoker (k := k)).obj (rightFreeObj (k := k) (S := S) M) := by
  let F := rightFreeFunctor (k := k) (R := R) (S := S)
  have h := LeftCoinduced.short_exact (k := k) M
  let := h.mono_f
  let := h.epi_g
  have hF : ((LeftCoinduced.short (k := k) M).map F).ShortExact := h.map F
  refine CokernelCofork.mapIsoOfIsColimit hF.gIsCokernel
    (coindShort_exact (rightFreeObj (k := k) (S := S) M)).gIsCokernel ?_
  refine Arrow.isoMk (Iso.refl _) (coindTensorIso M) ?_
  simpa only [F, LeftCoinduced.short, coindShort, ShortComplex.map, Arrow.mk,
    Iso.refl_hom, Category.id_comp] using (coindTensor_unit (k := k) (S := S) M).symm

def coindIterateTensorIso (M : ModuleCat R) : ∀ n : ℕ,
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.iterate (k := k) n).obj M) ≅
      (coindIterate (k := k) n).obj (rightFreeObj (k := k) (S := S) M)
  | 0 => Iso.refl _
  | n+1 => coindCokerTensorIso ((LeftCoinduced.iterate (k := k) n).obj M) ≪≫
      (coindCoker (k := k)).mapIso (coindIterateTensorIso M n)

def coindTermTensorIso (M : ModuleCat R) (n : ℕ) :
    rightFreeObj (k := k) (S := S)
      ((LeftCoinduced.J (k := k)).obj ((LeftCoinduced.iterate (k := k) n).obj M)) ≅
      coindTerm (rightFreeObj (k := k) (S := S) M) n :=
  coindTensorIso ((LeftCoinduced.iterate (k := k) n).obj M) ≪≫
    (coindEndo (k := k)).mapIso (coindIterateTensorIso M n)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftRegularObj : ModuleCat R := ModuleCat.of R R

def leftRegularUnderlying : leftRegularObj (R := R) ≃ₗ[k] R :=
  moduleCatUnderlyingEquiv (k := k) (R := R) R

def rightRegularUnderlying : rightRegularObj (S := S) ≃ₗ[k] Sᵐᵒᵖ :=
  moduleCatUnderlyingEquiv (k := k) (R := Sᵐᵒᵖ) Sᵐᵒᵖ

def regularOuterUnderlying :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≃ₗ[k] Alg k R S :=
  (rightFreeUnderlying _).trans
    (TensorProduct.congr (leftRegularUnderlying (k := k) (R := R))
      (rightRegularUnderlying (k := k) (S := S)))

lemma regularOuterUnderlying_tmul (r : leftRegularObj (R := R)) (s : rightRegularObj (S := S)) :
    regularOuterUnderlying (k := k) (r ⊗ₜ[k] s) = (show R from r) ⊗ₜ[k] (show Sᵐᵒᵖ from s) := rfl

def regularOuterEquiv :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≃ₗ[Alg k R S] Alg k R S where
  __ := (regularOuterUnderlying (k := k) (R := R) (S := S)).toAddEquiv
  map_smul' a z := by
    change regularOuterUnderlying (OuterTensor.action k R Sᵐᵒᵖ _ _ a z) =
      a * regularOuterUnderlying z
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,add_mul]
    | tmul a b =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => erw [map_add,map_add,hx,hy,map_add,mul_add]
      | tmul x y =>
        change (a*(show R from x)) ⊗ₜ[k] (b*(show Sᵐᵒᵖ from y)) =
          (a ⊗ₜ[k] b) * ((show R from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y))
        exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

def regularOuterIso :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≅ ModuleCat.of (Alg k R S) (Alg k R S) :=
  (regularOuterEquiv (k := k) (R := R) (S := S)).toModuleIso

lemma finiteProjective_inAdd_outer (M : ModuleCat (Alg k R S))
    [Module.Finite (Alg k R S) M] [Module.Projective (Alg k R S) M] :
    InAdd (rightFreeObj (k := k) (S := S) (leftRegularObj (R := R))) M := by
  obtain ⟨n,⟨r⟩⟩ := finiteProjective_inAdd M
  let e := biproduct.mapIso (fun _ : Fin n => (regularOuterIso (k := k) (R := R) (S := S)).symm)
  exact ⟨n,⟨r.trans e.retract⟩⟩

end Tachikawa.Enveloping


namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev coindComplex (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ((coindEndo (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

abbrev cokerComplex (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ((coindCoker (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

def coindComplexUnit (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) : P ⟶ coindComplex P where
  f i := coindUnit (P.X i)
  comm' i j _ := (coindUnitNat.naturality (P.d i j)).symm

def coindComplexπ (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) : coindComplex P ⟶ cokerComplex P where
  f i := coindπ (P.X i)
  comm' i j _ := ((cokernel.π (coindUnitNat (k := k))).naturality (P.d i j)).symm

def coindComplexShort (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :
    ShortComplex (CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ShortComplex.mk (coindComplexUnit P) (coindComplexπ P) (by
    apply HomologicalComplex.Hom.ext
    funext i
    exact coindUnit_π (P.X i))

lemma coindComplexShort_exact (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :
    (coindComplexShort P).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact coindShort_exact (P.X i)

end Tachikawa.Enveloping


namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
attribute [local instance] HasDerivedCategory.standard

lemma mappingCone_map_quasiIso {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map f g a b h) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  let t := DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap f g a b h)
  have h1 : IsIso t.hom₁ := by
    change IsIso (DerivedCategory.Q.map a)
    infer_instance
  have h2 : IsIso t.hom₂ := by
    change IsIso (DerivedCategory.Q.map b)
    infer_instance
  exact isIso₃_of_isIso₁₂ t (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g) h1 h2

end Tachikawa


namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def shortExactReplacementMap (S : ShortComplex (CochainComplex C ℤ))
    {Q : CochainComplex C ℤ} (α : S.X₃ ⟶ Q) : S.X₁ ⟶ mappingCocone (S.g ≫ α) :=
  let h := mappingCone.descShortComplex S ≫ α
  let w : mappingCone.inr S.f ≫ h = (𝟙 S.X₂) ≫ (S.g ≫ α) := by
    simp [h,← Category.assoc,mappingCone.inr_descShortComplex]
  (shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1) (by omega)).inv.app S.X₁ ≫
    ((mappingCone.rotateHomotopyEquiv S.f).hom ≫
      mappingCone.map (mappingCone.inr S.f) (S.g ≫ α) (𝟙 _) h w)⟦(-1 : ℤ)⟧'

lemma shortExactReplacementMap_quasiIso (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) {Q : CochainComplex C ℤ} (α : S.X₃ ⟶ Q) [QuasiIso α] :
    QuasiIso (shortExactReplacementMap S α) := by
  have := mappingCone.quasiIso_descShortComplex hS
  have : QuasiIso (mappingCone.descShortComplex S ≫ α) := inferInstance
  dsimp only [shortExactReplacementMap]
  have := mappingCone_map_quasiIso (mappingCone.inr S.f) (S.g ≫ α) (𝟙 S.X₂)
    (mappingCone.descShortComplex S ≫ α) (by
      simp [← Category.assoc,mappingCone.inr_descShortComplex])
  have hr : QuasiIso (mappingCone.rotateHomotopyEquiv S.f).hom :=
    (mappingCone.rotateHomotopyEquiv S.f).quasiIso_hom
  have hc : QuasiIso ((mappingCone.rotateHomotopyEquiv S.f).hom ≫
      mappingCone.map (mappingCone.inr S.f) (S.g ≫ α) (𝟙 S.X₂)
        (mappingCone.descShortComplex S ≫ α) (by
          simp [← Category.assoc,mappingCone.inr_descShortComplex])) := inferInstance
  have hs := (CochainComplex.quasiIso_shift_iff _ (-1)).2 hc
  have he : QuasiIso
      ((shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1) (by omega)).inv.app S.X₁) := by
    exact quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := he) (hφ' := hs)

end Tachikawa


namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

structure CoindReplacement (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) where
  complex : CochainComplex (ModuleCat (Alg k R S)) ℤ
  map : P ⟶ complex
  quasiIso : QuasiIso map

attribute [instance] CoindReplacement.quasiIso

def coindReplacement : (n : ℕ) → (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) → CoindReplacement P
  | 0, P => ⟨P,𝟙 P,inferInstance⟩
  | n+1, P =>
    let t := coindReplacement n (cokerComplex P)
    { complex := mappingCocone (coindComplexπ P ≫ t.map)
      map := shortExactReplacementMap (coindComplexShort P) t.map
      quasiIso := by
        exact @shortExactReplacementMap_quasiIso _ _ _ (coindComplexShort P)
          (coindComplexShort_exact P) _ t.map t.quasiIso }

def CoindGoodTerms (W : ModuleCat (Alg k R S)) :
    ℕ → CochainComplex (ModuleCat (Alg k R S)) ℤ → Prop
  | 0, P => ∀ i, InAdd W (P.X i)
  | n+1, P => (∀ i, InAdd W ((coindComplex P).X i)) ∧ CoindGoodTerms W n (cokerComplex P)

lemma mappingCocone_inAdd {W : ModuleCat (Alg k R S)}
    {K L : CochainComplex (ModuleCat (Alg k R S)) ℤ} (f : K ⟶ L)
    (hK : ∀ i, InAdd W (K.X i)) (hL : ∀ i, InAdd W (L.X i)) (i : ℤ) :
    InAdd W ((mappingCocone f).X i) := by
  let e : (mappingCocone f).X i ≅ K.X i ⊞ L.X (i + -1) :=
    shiftFunctorObjXIso (mappingCone f) (-1) i (i + -1) (by omega) ≪≫
      homotopyCofiber.XIsoBiprod f (i + -1) i (by change (i + -1) + 1 = i; omega)
  exact ((hK i).biprod (hL (i + -1))).iso e

lemma coindReplacement_terms (W : ModuleCat (Alg k R S)) (n : ℕ)
    (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) (h : CoindGoodTerms W n P) :
    ∀ i, InAdd W ((coindReplacement n P).complex.X i) := by
  induction n generalizing P with
  | zero => exact h
  | succ n ih =>
    exact mappingCocone_inAdd _ h.1 (ih (cokerComplex P) h.2)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma mappingCocone_isZero_X {K L : CochainComplex (ModuleCat (Alg k R S)) ℤ}
    (f : K ⟶ L) (i : ℤ) (hK : IsZero (K.X i)) (hL : IsZero (L.X (i-1))) :
    IsZero ((mappingCocone f).X i) := by
  let e : (mappingCocone f).X i ≅ K.X i ⊞ L.X (i-1) :=
    shiftFunctorObjXIso (mappingCone f) (-1) i (i-1) (by omega) ≪≫
      homotopyCofiber.XIsoBiprod f (i-1) i (by change i-1+1=i; omega)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hK,hL⟩) e

lemma coindReplacement_bounded (n : ℕ)
    (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) (l u : ℤ)
    (hP : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∀ i, i < l ∨ u + n < i → IsZero ((coindReplacement n P).complex.X i) := by
  induction n generalizing P with
  | zero => simpa only [coindReplacement, Nat.cast_zero, add_zero] using hP
  | succ n ih =>
    intro i hi
    apply mappingCocone_isZero_X
    · exact (coindEndo (k := k)).map_isZero (hP i (by omega))
    · apply ih (cokerComplex P)
      · intro j hj
        exact (coindCoker (k := k)).map_isZero (hP j hj)
      · omega

end Tachikawa.Enveloping


end
end OAI
