import OAI.RingTheory.Tachikawa.CycleQuasiIso
import OAI.RingTheory.Tachikawa.OuterTensor

/-! Characteristic-independent excerpts from pinned OpenAI Math (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
instance downIntTensorSigns : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : q+1=p) := by
    change q + r + 1 = p + r
    omega
  add_rel p q r (hpq : q+1=p) := by
    change r + q + 1 = r + p
    omega
  ε'_succ := by
    rintro _ q rfl
    change Int.negOnePow q = -Int.negOnePow (q + 1)
    rw [Int.negOnePow_succ, neg_neg]

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type} [Field k]

lemma zeroDifferential_isIso_of_quasiIso
    {K L : ChainComplex (ModuleCat k) ℤ} (f : K ⟶ L)
    (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0) [QuasiIso f] : IsIso f := by
  have (j : ℤ) : IsIso (f.f j) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hh := shortComplex_cycles_of_quasiIso _
      ((quasiIsoAt_iff' f (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨z,hz⟩ := hh.1 x (by change K.d j (j-1) x = 0; rw [hK]; rfl)
        ⟨0, by change L.d (j+1) j 0 = f.f j x; rw [map_zero]; exact hx.symm⟩
      change K.d (j+1) j z = x at hz
      rw [hK] at hz
      exact hz.symm
    · intro y
      obtain ⟨x,_,z,hz⟩ := hh.2 y (by change L.d j (j-1) y = 0; rw [hL]; rfl)
      refine ⟨x, ?_⟩
      change L.d (j+1) j z = f.f j x - y at hz
      rw [hL] at hz
      exact sub_eq_zero.mp hz.symm
  exact HomologicalComplex.Hom.isIso_of_components f

lemma vectorTensor_quasiIso_int
    {K L M N : ChainComplex (ModuleCat k) ℤ} (f : K ⟶ L) (g : M ⟶ N)
    [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)) (.down ℤ)) := by
  let F := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)
  let ef := VectorSplit.homologyHomotopyEquiv K
  let el := VectorSplit.homologyHomotopyEquiv L
  let em := VectorSplit.homologyHomotopyEquiv M
  let en := VectorSplit.homologyHomotopyEquiv N
  let := ef.quasiIso_inv
  let := el.quasiIso_hom
  let := em.quasiIso_inv
  let := en.quasiIso_hom
  let f' := ef.inv ≫ f ≫ el.hom
  let g' := em.inv ≫ g ≫ en.hom
  have : IsIso f' := zeroDifferential_isIso_of_quasiIso f' (fun _ _ => rfl) (fun _ _ => rfl)
  have : IsIso g' := zeroDifferential_isIso_of_quasiIso g' (fun _ _ => rfl) (fun _ _ => rfl)
  let ei := bifunctorHomotopyEquiv F (.down ℤ) ef.symm em.symm
  let ep := bifunctorHomotopyEquiv F (.down ℤ) el en
  let := ei.quasiIso_hom
  let := ep.quasiIso_hom
  have hh : QuasiIso (ei.hom ≫ mapBifunctorMap f g F (.down ℤ) ≫ ep.hom) := by
    change QuasiIso (mapBifunctorMap ef.inv em.inv F (.down ℤ) ≫
      mapBifunctorMap f g F (.down ℤ) ≫ mapBifunctorMap el.hom en.hom F (.down ℤ))
    rw [bifunctorMap_comp, bifunctorMap_comp]
    change QuasiIso (mapBifunctorMap f' g' F (.down ℤ))
    exact (bifunctorHomotopyEquiv F (.down ℤ) (HomotopyEquiv.ofIso (asIso f')) (HomotopyEquiv.ofIso (asIso g'))).quasiIso_hom
  exact (quasiIso_iff_comp_right _ ep.hom).mp ((quasiIso_iff_comp_left ei.hom _).mp hh)

end Tachikawa

namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {K K' : ChainComplex (ModuleCat A) ℤ} {L L' : ChainComplex (ModuleCat B) ℤ}

instance restrictionPreservesHomology {R S : Type} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars f).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

lemma quasiIso_int (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (.down ℤ)) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (forgetE k A B)).mp
  rw [← quasiIso_iff_comp_right _ (forgetTotalIso k A B K' L' (.down ℤ)).hom,
    forgetTotalIso_natural]
  have := vectorTensor_quasiIso_int (((forgetA k A).mapHomologicalComplex (.down ℤ)).map f)
    (((forgetB k B).mapHomologicalComplex (.down ℤ)).map g)
  infer_instance

end Tachikawa.OuterTensor

end
end OAI
