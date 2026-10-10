import OAI.RingTheory.Tachikawa.InductionQuasiIso

/-! Characteristic-independent balanced induction comparison from pinned OpenAI Math.
Apache-2.0; excerpt declarations unchanged, imports and wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev inclusion : R →ₐ[k] TrivialExtension k R :=
  TrivSqZeroExt.inlAlgHom k R (DualBimodule k R)

def tensorGenerators (M : ModuleCat.{0} R) : M ⟶
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj
      ((functor (k := k) (R := R)).obj M) :=
  ModuleCat.ofHom
    (X := M)
    (Y := (AlgebraInduction.res (inclusion (k := k) (R := R))).obj
      ((functor (k := k) (R := R)).obj M))
    { toFun := fun m => (show Obj k R M from (m,0))
      map_add' := by
        intro x y
        apply Prod.ext
        · rfl
        · exact (zero_add _).symm
      map_smul' := by
        intro r m
        change (r • m, (0 : Nakayama k R M)) =
          (TrivSqZeroExt.inl r : TrivialExtension k R) • (show Obj k R M from (m,0))
        rw [inl_smul]
        apply Prod.ext
        · rfl
        · exact (smul_zero r).symm }

def tensorComparison (M : ModuleCat.{0} R) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ⟶
      (functor (k := k) (R := R)).obj M :=
  AlgebraInduction.extend (inclusion (k := k) (R := R)) (tensorGenerators M)

@[simp] lemma tensorComparison_mk (M : ModuleCat.{0} R)
    (a : AlgebraInduction.Bimod (inclusion (k := k) (R := R))) (m : M) :
    tensorComparison (k := k) M (BalancedTensor.mk a m) =
      (show TrivialExtension k R from a) • unit m := rfl

def tensorPure (M : ModuleCat.{0} R) :
    AlgebraInduction.Bimod (inclusion (k := k) (R := R)) →ₗ[TrivialExtension k R]
      M →ₗ[k] BalancedTensor.T (k := k) (R := R) (S := TrivialExtension k R)
        (M := AlgebraInduction.Bimod (inclusion (k := k) (R := R))) (N := M) :=
  BalancedTensor.mk

lemma tensorPure_inr_smul (M : ModuleCat.{0} R) (r : R) (φ : DualBimodule k R) (m : M) :
    tensorPure (k := k) M
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (r • φ) : TrivialExtension k R)) m =
    (TrivSqZeroExt.inl r : TrivialExtension k R) • tensorPure (k := k) M
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) m := by
  have h := LinearMap.congr_fun ((tensorPure (k := k) M).map_smul
    (TrivSqZeroExt.inl r : TrivialExtension k R)
    (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (TrivSqZeroExt.inr φ : TrivialExtension k R))) m
  have hr : (TrivSqZeroExt.inl r : TrivialExtension k R) •
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) =
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (r • φ) : TrivialExtension k R)) :=
    TrivSqZeroExt.inl_mul_inr r φ
  rw [hr] at h
  exact h

def lowerBilinear (M : ModuleCat.{0} R) : DualBimodule k R →ₗ[R] M →ₗ[k]
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj ((AlgebraInduction.functor (inclusion (k := k))).obj M) where
  toFun φ :=
    { toFun := fun m => tensorPure (k := k) M (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) m
      map_add' := fun x y => (tensorPure (k := k) M _).map_add x y
      map_smul' := by
        intro c x
        change tensorPure (k := k) M _ (c • x) = (algebraMap k (TrivialExtension k R) c) • tensorPure (k := k) M _ x
        rw [IsScalarTower.algebraMap_smul]
        exact (tensorPure (k := k) M _).map_smul c x }
  map_add' φ ψ := by
    apply LinearMap.ext
    intro m
    change tensorPure (k := k) M (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
      (TrivSqZeroExt.inr (φ+ψ) : TrivialExtension k R)) m = _
    rw [TrivSqZeroExt.inr_add]
    exact LinearMap.congr_fun ((tensorPure (k := k) M).map_add _ _) m
  map_smul' r φ := by
    apply LinearMap.ext
    intro m
    exact tensorPure_inr_smul M r φ m

lemma lowerBilinear_balanced (M : ModuleCat.{0} R) (r : R) (φ : DualBimodule k R) (m : M) :
    lowerBilinear (k := k) M (MulOpposite.op r • φ) m = lowerBilinear (k := k) M φ (r • m) := by
  have h := BalancedTensor.balance (k := k) (R := R) (S := TrivialExtension k R)
    r (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (TrivSqZeroExt.inr φ : TrivialExtension k R)) m
  have hr : MulOpposite.op r •
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) =
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (MulOpposite.op r • φ) : TrivialExtension k R)) :=
    TrivSqZeroExt.inr_mul_inl r φ
  rw [hr] at h
  exact h

def lowerTensor (M : ModuleCat.{0} R) :
    BalancedTensor.T (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) →ₗ[R]
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj ((AlgebraInduction.functor (inclusion (k := k))).obj M) :=
  BalancedTensor.lift (lowerBilinear (k := k) M) (lowerBilinear_balanced M)

variable [FiniteDimensional k R] (M : ModuleCat.{0} R) [FiniteDimensional k M]

def tensorInverse (x : Obj k R M) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M :=
  AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 +
    lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)

omit [FiniteDimensional k R] [FiniteDimensional k M] in
lemma tensorComparison_lower (z : BalancedTensor.T (k := k) (R := R) (S := R)
    (M := DualBimodule k R) (N := M)) :
    tensorComparison (k := k) M (lowerTensor (k := k) M z) = (0, Nakayama.evaluation z) := by
  induction z using BalancedTensor.induction_on with
  | h0 => rfl
  | ht φ m =>
    apply Prod.ext
    · change (0:R) • m = 0
      simp
    · change Nakayama.evaluationBilinear φ m + (0:R) • (0 : Nakayama k R M) = _
      rw [zero_smul, add_zero]
      rfl
  | ha x y hx hy =>
    erw [map_add, map_add, hx, hy, map_add]
    apply Prod.ext
    · exact zero_add _
    · rfl

lemma tensorComparison_inverse (x : Obj k R M) :
    tensorComparison (k := k) M (tensorInverse (k := k) M x) = x := by
  change tensorComparison (k := k) M (AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 +
    lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)) = x
  erw [map_add, tensorComparison_lower]
  have he := (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).apply_symm_apply x.2
  change Nakayama.evaluation ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2) = x.2 at he
  rw [he]
  change (1 : TrivialExtension k R) • unit x.1 + (0,x.2) = x
  erw [one_smul]
  apply Prod.ext
  · exact add_zero _
  · exact zero_add _

lemma tensorInverse_zero : tensorInverse (k := k) M 0 = 0 := by
  change AlgebraInduction.unit (inclusion (k := k) (R := R)) M 0 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm 0) = 0
  simp

lemma tensorInverse_add (x y : Obj k R M) :
    tensorInverse (k := k) M (x+y) = tensorInverse (k := k) M x + tensorInverse (k := k) M y := by
  change AlgebraInduction.unit (inclusion (k := k) (R := R)) M (x.1+y.1) + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm (x.2+y.2)) = _
  simp only [map_add]
  change _ = (AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)) +
    (AlgebraInduction.unit (inclusion (k := k) (R := R)) M y.1 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm y.2))
  abel

lemma tensorInverse_comparison (z : (AlgebraInduction.functor
    (inclusion (k := k) (R := R))).obj M) :
    tensorInverse (k := k) M (tensorComparison (k := k) M z) = z := by
  induction z using BalancedTensor.induction_on with
  | h0 =>
    exact (congrArg (tensorInverse (k := k) M)
      (tensorComparison (k := k) M).hom.map_zero).trans (tensorInverse_zero M)
  | ha x y hx hy =>
    erw [map_add, tensorInverse_add, hx, hy]
    rfl
  | ht a m =>
    have he : (tensorComparison (k := k) M (BalancedTensor.mk a m) : Obj k R M) =
        ((show TrivialExtension k R from a).fst • m,
          Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m) := by
      apply Prod.ext
      · rfl
      · change Nakayama.evaluationBilinear _ m + _ • (0 : Nakayama k R M) = _
        rw [smul_zero, add_zero]
    rw [he]
    change AlgebraInduction.unit (inclusion (k := k) (R := R)) M ((show TrivialExtension k R from a).fst • m) +
      lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm
        (Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m)) = _
    have hinv : (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm
        (Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m) =
        BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) (show TrivialExtension k R from a).snd m := by
      have h := (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm_apply_apply
        (BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) (show TrivialExtension k R from a).snd m)
      exact h
    rw [hinv]
    change BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R)
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (1 : TrivialExtension k R)) ((show TrivialExtension k R from a).fst • m) +
      BalancedTensor.mk (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        TrivSqZeroExt.inr (show TrivialExtension k R from a).snd) m = _
    rw [← BalancedTensor.balance]
    change BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R)
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (1 : TrivialExtension k R) * TrivSqZeroExt.inl
        (show TrivialExtension k R from a).fst) m +
      BalancedTensor.mk (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        TrivSqZeroExt.inr (show TrivialExtension k R from a).snd) m = _
    erw [one_mul]
    erw [← LinearMap.add_apply, ← map_add]
    exact congrArg (fun t : AlgebraInduction.Bimod (inclusion (k := k) (R := R)) =>
      BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R) t m)
      (TrivSqZeroExt.inl_fst_add_inr_snd_eq (show TrivialExtension k R from a))

def tensorComparisonEquiv :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ≃ₗ[TrivialExtension k R]
      (functor (k := k) (R := R)).obj M :=
  LinearEquiv.ofBijective (tensorComparison (k := k) M).hom
    ⟨Function.LeftInverse.injective (tensorInverse_comparison M),
      Function.RightInverse.surjective (tensorComparison_inverse M)⟩

def tensorComparisonIso :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ≅
      (functor (k := k) (R := R)).obj M :=
  LinearEquiv.toModuleIso (tensorComparisonEquiv M)

end Tachikawa.TrivialInduction



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

lemma tensorComparison_natural {M N : ModuleCat.{0} R} (f : M ⟶ N) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).map f ≫
      tensorComparison (k := k) N =
    tensorComparison (k := k) M ≫ (functor (k := k)).map f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro a m
  change (show TrivialExtension k R from a) • unit (f m) =
    map (k := k) (R := R) f.hom ((show TrivialExtension k R from a) • unit m)
  rw [map_smul, map_unit]

variable [FiniteDimensional k R]

def tensorComplexIso {ι : Type} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{0} R) c)
    [∀ i, FiniteDimensional k (P.X i)] :
    (((AlgebraInduction.functor (inclusion (k := k) (R := R))).mapHomologicalComplex c).obj P) ≅
      (((functor (k := k) (R := R)).mapHomologicalComplex c).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => tensorComparisonIso (P.X i)) (fun i j _ => (tensorComparison_natural (P.d i j)).symm)

end Tachikawa.TrivialInduction

end
end OAI
