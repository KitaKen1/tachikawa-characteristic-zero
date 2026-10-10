import TachikawaCharZero.SignedTotal
import OAI.RingTheory.Tachikawa.OuterTensor

/-! Künneth for actual ordinary Ext over tensor-product algebras, over any
field. Generic projective-resolution and vector-space splitting arguments
are adapted from OpenAI Math's Tachikawa/OuterExt.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The Hom/total comparison uses the local signed theorem, with no CharP 2
assumption. This module establishes vector-space comparison, not the
Yoneda-product interchange law. -/
open OAI.Tachikawa OAI.Tachikawa.OuterTensor OAI.Tachikawa.VectorSplit




noncomputable section
namespace TachikawaCharZero.TensorExt
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k]
  {K L M N : ChainComplex (ModuleCat k) ℕ}

theorem vectorTensor_quasiIso (f : K ⟶ L) (g : M ⟶ N) [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)) (.down ℕ)) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  obtain ⟨e', he'⟩ := (ChainComplex.quasiIso_iff_of_projective g).mp inferInstance
  rw [← he, ← he']
  exact (bifunctorHomotopyEquiv _ (.down ℕ) e e').quasiIso_hom

end TachikawaCharZero.TensorExt



namespace TachikawaCharZero.TensorExt
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {K K' : ChainComplex (ModuleCat A) ℕ} {L L' : ChainComplex (ModuleCat B) ℕ}

instance restrictionPreservesHomology {R S : Type} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars f).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

theorem quasiIso (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (.down ℕ)) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (forgetE k A B)).mp
  rw [← quasiIso_iff_comp_right _ (forgetTotalIso k A B K' L' (.down ℕ)).hom,
    forgetTotalIso_natural]
  have := vectorTensor_quasiIso (((forgetA k A).mapHomologicalComplex (.down ℕ)).map f)
    (((forgetB k B).mapHomologicalComplex (.down ℕ)).map g)
  infer_instance

end TachikawaCharZero.TensorExt



namespace TachikawaCharZero.TensorExt
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]

def bifunctorZeroIso (K : ChainComplex C₁ ℕ) (L : ChainComplex C₂ ℕ)
    [HasMapBifunctor K L F (.down ℕ)] :
    (mapBifunctor K L F (.down ℕ)).X 0 ≅ (F.obj (K.X 0)).obj (L.X 0) where
  hom := mapBifunctorDesc (fun i j h => eqToHom (by
    have hh : i + j = 0 := h
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hh
    rfl))
  inv := ιMapBifunctor K L F (.down ℕ) 0 0 0 rfl
  hom_inv_id := by
    apply mapBifunctor.hom_ext
    intro i j h
    have hh : i + j = 0 := h
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hh
    rw [ι_mapBifunctorDesc_assoc]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  inv_hom_id := by rw [ι_mapBifunctorDesc]; rfl

variable (M : C₁) (N : C₂)
variable [HasMapBifunctor ((ChainComplex.single₀ C₁).obj M)
  ((ChainComplex.single₀ C₂).obj N) F (.down ℕ)]
abbrev singleBifunctor := mapBifunctor ((ChainComplex.single₀ C₁).obj M)
  ((ChainComplex.single₀ C₂).obj N) F (.down ℕ)

omit [HasZeroObject D] in
theorem singleBifunctor_isZero (n : ℕ) (hn : n ≠ 0) : IsZero ((singleBifunctor F M N).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j h
  rw [Category.comp_id, comp_zero]
  have hij : i + j = n := h
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by omega
    exact ((F.obj _).map_isZero
      (isZero_single_obj_X (.down ℕ) 0 N j hj)).eq_of_src _ _
  · exact ((F.flip.obj _).map_isZero
      (isZero_single_obj_X (.down ℕ) 0 M i hi)).eq_of_src _ _

def bifunctorSingleIso : singleBifunctor F M N ≅
    (ChainComplex.single₀ D).obj ((F.obj M).obj N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => if hn : n = 0 then by
      subst n
      exact bifunctorZeroIso F _ _
    else (singleBifunctor_isZero F M N n hn).iso
      (isZero_single_obj_X (.down ℕ) 0 ((F.obj M).obj N) n hn)) (by
      intro i j hij
      cases i with
      | zero => simp only [ComplexShape.down_Rel] at hij; omega
      | succ i => exact (singleBifunctor_isZero F M N (i+1) (by omega)).eq_of_src _ _)

end TachikawaCharZero.TensorExt



namespace TachikawaCharZero.TensorExt
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (hP : ∀ n, Module.Finite A (P.complex.X n))
  (hQ : ∀ n, Module.Finite B (Q.complex.X n))

include hP hQ in
theorem total_projective (n : ℕ) :
    Projective ((mapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ)).X n) := by
  let (i : ℕ) : Module.Finite A (P.complex.X i) := hP i
  let (i : ℕ) : Module.Finite B (Q.complex.X i) := hQ i
  have (i j : ℕ) : Module.Projective (A ⊗[k] B)
      (Obj k A B (P.complex.X i) (Q.complex.X j)) := projective k A B _ _
  have (i j : ℕ) : Projective
      (((bifunctor k A B).obj (P.complex.X i)).obj (Q.complex.X j)) := by
    change Projective (ModuleCat.of (A ⊗[k] B) (Obj k A B (P.complex.X i) (Q.complex.X j)))
    infer_instance
  change Projective (∐ fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
    ((bifunctor k A B).obj (P.complex.X ij.val.1)).obj (Q.complex.X ij.val.2))
  infer_instance

def resolution : ProjectiveResolution ((bifunctor k A B).obj M |>.obj N) where
  complex := mapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ)
  projective := total_projective k A B P Q hP hQ
  π := mapBifunctorMap P.π Q.π (bifunctor k A B) (.down ℕ) ≫
    (bifunctorSingleIso (bifunctor k A B) M N).hom
  quasiIso := by
    have := quasiIso k A B P.π Q.π
    infer_instance

end TachikawaCharZero.TensorExt




namespace TachikawaCharZero.TensorExt
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (P : ChainComplex (ModuleCat A) ℕ) (Q : ChainComplex (ModuleCat B) ℕ)
  (U : ModuleCat A) (V : ModuleCat B)

abbrev homBicomplex := ((tensorF k).mapBifunctorHomologicalComplex (.up ℕ) (.up ℕ)).obj
  (resolutionHom k A P U) |>.obj (resolutionHom k B Q V)

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Finite B (Q.X n)]
  [∀ n, Module.Projective A (P.X n)] [∀ n, Module.Projective B (Q.X n)]
  [∀ n, FiniteDimensional k (P.X n)] [∀ n, FiniteDimensional k (Q.X n)]

def homBicomplexEquiv (i j : ℕ) : ((homBicomplex (k := k) P Q U V).X i).X j ≃ₗ[k]
    (((outerBicomplex k A B P Q).X i).X j ⟶ ((bifunctor k A B).obj U).obj V) :=
  homEquiv (k := k) (P.X i) U (Q.X j) V

theorem precompose_id {M U : ModuleCat A} :
    precompose (k := k) (U := U) (𝟙 M) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact Category.id_comp f

theorem homBicomplexEquiv_horizontal (i j : ℕ) (x : ((homBicomplex (k := k) P Q U V).X i).X j) :
    homBicomplexEquiv P Q U V (i+1) j ((homBicomplex (k := k) P Q U V).d i (i+1) |>.f j <| x) =
      ((outerBicomplex k A B P Q).d (i+1) i).f j ≫ homBicomplexEquiv P Q U V i j x := by
  change (P.X i ⟶ U) ⊗[k] (Q.X j ⟶ V) at x
  change homMap (TensorProduct.map (precompose (k := k) (P.d (i+1) i)) LinearMap.id x) =
    morphism (P.d (i+1) i) (𝟙 (Q.X j)) ≫ homMap x
  have h := homMap_precompose (P.d (i+1) i) (𝟙 (Q.X j)) x
  rw [precompose_id] at h
  exact h

theorem homBicomplexEquiv_vertical (i j : ℕ) (x : ((homBicomplex (k := k) P Q U V).X i).X j) :
    homBicomplexEquiv P Q U V i (j+1) (((homBicomplex (k := k) P Q U V).X i).d j (j+1) x) =
      ((outerBicomplex k A B P Q).X i).d (j+1) j ≫ homBicomplexEquiv P Q U V i j x := by
  change (P.X i ⟶ U) ⊗[k] (Q.X j ⟶ V) at x
  change homMap (TensorProduct.map LinearMap.id (precompose (k := k) (Q.d (j+1) j)) x) =
    morphism (𝟙 (P.X i)) (Q.d (j+1) j) ≫ homMap x
  have h := homMap_precompose (𝟙 (P.X i)) (Q.d (j+1) j) x
  rw [precompose_id] at h
  exact h


def homTotalIso :
    mapBifunctor (resolutionHom k A P U) (resolutionHom k B Q V) (tensorF k) (.up ℕ) ≅
    resolutionHom k (A ⊗[k] B) (mapBifunctor P Q (bifunctor k A B) (.down ℕ))
      (((bifunctor k A B).obj U).obj V) :=
  SignedTotalPairing.iso (outerBicomplex k A B P Q) (homBicomplex (k := k) P Q U V) _
    (homBicomplexEquiv P Q U V) (homBicomplexEquiv_horizontal P Q U V)
    (homBicomplexEquiv_vertical P Q U V)

end TachikawaCharZero.TensorExt



namespace TachikawaCharZero.TensorExt
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

def homologyIsoH (K : HomologicalComplex (ModuleCat k) c) (i : I) :
    K.homology i ≅ ModuleCat.of k (H K i) :=
  (homologyHomotopyEquiv K).toHomologyIso i ≪≫
    zeroDifferentialHomologyIso (homologyComplex K) (fun _ _ => rfl) i

end TachikawaCharZero.TensorExt



namespace TachikawaCharZero.TensorExt
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M U : ModuleCat A} {N V : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)] [∀ n, FiniteDimensional k (Q.complex.X n)]

abbrev tensorResolution := resolution k A B P Q (fun _ => inferInstance) (fun _ => inferInstance)
abbrev homologyTensor := mapBifunctor
  (VectorSplit.homologyComplex (resolutionHom k A P.complex U))
  (VectorSplit.homologyComplex (resolutionHom k B Q.complex V)) (tensorF k) (.up ℕ)

def extKunneth (n : ℕ) :
    Ext (((bifunctor k A B).obj M).obj N) (((bifunctor k A B).obj U).obj V) n ≃ₗ[k]
      (∀ t : SignedTotalPairing.Diag n, Ext M U t.val.1 ⊗[k] Ext N V t.val.2) := by
  let S := tensorResolution (k := k) P Q
  let H := resolutionHom k (A ⊗[k] B) S.complex (((bifunctor k A B).obj U).obj V)
  let e₁ := (resolutionHomologyExtAll (N := ((bifunctor k A B).obj U).obj V) S n (k := k)).symm
  let e₂ := (homologyIsoH H n).symm.toLinearEquiv
  let e₃ := ((homologyFunctor (ModuleCat k) (.up ℕ) n).mapIso
    (homTotalIso P.complex Q.complex U V).symm).toLinearEquiv
  let e₄ := (VectorSplit.tensorHomologyIso (resolutionHom k A P.complex U)
    (resolutionHom k B Q.complex V) (.up ℕ) n).toLinearEquiv
  let e₅ := coproductPiEquiv (fun t : SignedTotalPairing.Diag n =>
    ModuleCat.of k (VectorSplit.H (resolutionHom k A P.complex U) t.val.1 ⊗[k]
      VectorSplit.H (resolutionHom k B Q.complex V) t.val.2))
  let e₆ := LinearEquiv.piCongrRight (fun t : SignedTotalPairing.Diag n =>
    TensorProduct.congr (resolutionHomologyExtAll (N := U) P t.val.1 (k := k))
      (resolutionHomologyExtAll (N := V) Q t.val.2 (k := k)))
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

end TachikawaCharZero.TensorExt



