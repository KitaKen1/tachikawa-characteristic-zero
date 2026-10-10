import OAI.RingTheory.Tachikawa.GenericBimoduleFiber

/-! A stable-zero sum admits a kernel lift with two prescribed projections.
The correction uses the covering summand, whose two projections vanish.
Keeping this argument over an abstract ring avoids expanding the concrete
rational enveloping algebra during kernel checking. -/
namespace TachikawaCharZero.StableFiberPair
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {X A B C D U V : ModuleCat R}

theorem exists_pair (i : C ⟶ B) (p : B ⟶ D) (j : A ⟶ B)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hj : Function.Surjective (j ≫ p))
    (a₁ a₂ : X ⟶ B) (r₁ : B ⟶ U) (r₂ : B ⟶ V)
    (s₁ : X ⟶ U) (s₂ : X ⟶ V)
    (hz : stableClass (k:=k) ((a₁+a₂) ≫ p).hom = 0)
    (h₁₁ : a₁ ≫ r₁ = s₁) (h₂₁ : a₂ ≫ r₁ = 0) (hj₁ : j ≫ r₁ = 0)
    (h₁₂ : a₁ ≫ r₂ = 0) (h₂₂ : a₂ ≫ r₂ = s₂) (hj₂ : j ≫ r₂ = 0) :
    ∃ v : X ⟶ C, (v ≫ i) ≫ r₁ = s₁ ∧ (v ≫ i) ≫ r₂ = s₂ := by
  obtain ⟨v,b,hv⟩ := exists_stable_kernel_lift i p j hi he hj (a₁+a₂) hz
  refine ⟨v,?_,?_⟩
  · rw [hv,Preadditive.sub_comp,Preadditive.add_comp,Category.assoc,
      h₁₁,h₂₁,hj₁,comp_zero,add_zero,sub_zero]
  · rw [hv,Preadditive.sub_comp,Preadditive.add_comp,Category.assoc,
      h₁₂,h₂₂,hj₂,comp_zero,zero_add,sub_zero]

section Evaluated
variable [FiniteDimensional k R]

theorem exists_evaluated_pair (X : ModuleCat R) (U V Y : FiniteModule k (Enveloping.Alg k R R))
    (g₀ : U.obj ⟶ Y.obj) (h₀ : V.obj ⟶ Y.obj)
    (eU : Enveloping.evalObj X U.obj ≅ X) (eV : Enveloping.evalObj X V.obj ≅ X)
    (hi : Function.Injective
      (Enveloping.evalMap X (Enveloping.fiberInclusion U V Y g₀ (-h₀))))
    (he : Function.Exact
      (Enveloping.evalMap X (Enveloping.fiberInclusion U V Y g₀ (-h₀)))
      (Enveloping.evalMap X (Enveloping.fiberProjection U V Y g₀ (-h₀))))
    (hz : stableClass (k:=k) (eU.inv ≫ Enveloping.evalMap X g₀).hom =
      stableClass (k:=k) (eV.inv ≫ Enveloping.evalMap X h₀).hom) :
    ∃ v : X ⟶ Enveloping.evalObj X (Enveloping.fiber U V Y g₀ (-h₀)).obj,
      v ≫ Enveloping.evalMap X
        (Enveloping.fiberInclusion U V Y g₀ (-h₀) ≫ Enveloping.fiberFst U V Y) = eU.inv ∧
      v ≫ Enveloping.evalMap X
        (Enveloping.fiberInclusion U V Y g₀ (-h₀) ≫ Enveloping.fiberSnd U V Y) = eV.inv := by
  let L := Enveloping.evaluation (k:=k) (S:=R) X
  let u := U
  let w := V
  let g := g₀
  let h := -h₀
  let i := L.map (Enveloping.fiberInclusion U V Y g₀ (-h₀))
  let p := L.map (Enveloping.fiberProjection U V Y g₀ (-h₀))
  let j := L.map (Enveloping.fiberInr u w Y)
  let a := eU.inv ≫ L.map (Enveloping.fiberInl u w Y) +
    eV.inv ≫ L.map (Enveloping.fiberInm u w Y)
  have hap : a ≫ p = (eU.inv ≫ Enveloping.evalMap X g₀) -
      (eV.inv ≫ Enveloping.evalMap X h₀) := by
    change (_+_) ≫ L.map (Enveloping.fiberProjection u w Y g h) = _
    rw [Preadditive.add_comp,Category.assoc,Category.assoc,← L.map_comp,← L.map_comp,
      Enveloping.fiberInl_projection,Enveloping.fiberInm_projection]
    change _ + _ ≫ L.map (-h₀) = _
    rw [L.map_neg,Preadditive.comp_neg]
    exact (sub_eq_add_neg _ _).symm
  have haz : stableClass (k:=k) (a ≫ p).hom=0 := by
    rw [hap]
    change stableClass (k:=k) (((eU.inv ≫ Enveloping.evalMap X g₀)).hom -
      ((eV.inv ≫ Enveloping.evalMap X h₀)).hom)=0
    rw [map_sub,hz,sub_self]
  have hjp : j ≫ p = L.map (ModuleCat.ofHom Y.cover.map) := by
    rw [← L.map_comp]
    exact congrArg L.map (Enveloping.fiberInr_projection u w Y g h)
  have hj : Function.Surjective (j ≫ p) := by
    rw [hjp]
    exact Enveloping.evalMap_surjective X _ Y.cover.surjective
  have h₁₁ : (eU.inv ≫
      L.map (Enveloping.fiberInl u w Y)) ≫ L.map (Enveloping.fiberFst u w Y) =
      eU.inv := by
    rw [Category.assoc,← L.map_comp,Enveloping.fiberInl_fst,L.map_id]
    exact Category.comp_id eU.inv
  have h₂₁ : (eV.inv ≫
      L.map (Enveloping.fiberInm u w Y)) ≫ L.map (Enveloping.fiberFst u w Y) = 0 := by
    rw [Category.assoc,← L.map_comp,Enveloping.fiberInm_fst,L.map_zero,comp_zero]
  have hj₁ : j ≫ L.map (Enveloping.fiberFst u w Y) = 0 := by
    rw [← L.map_comp,Enveloping.fiberInr_fst,L.map_zero]
  have h₁₂ : (eU.inv ≫
      L.map (Enveloping.fiberInl u w Y)) ≫ L.map (Enveloping.fiberSnd u w Y) = 0 := by
    rw [Category.assoc,← L.map_comp,Enveloping.fiberInl_snd,L.map_zero,comp_zero]
  have h₂₂ : (eV.inv ≫
      L.map (Enveloping.fiberInm u w Y)) ≫ L.map (Enveloping.fiberSnd u w Y) =
      eV.inv := by
    rw [Category.assoc,← L.map_comp,Enveloping.fiberInm_snd,L.map_id]
    exact Category.comp_id eV.inv
  have hj₂ : j ≫ L.map (Enveloping.fiberSnd u w Y) = 0 := by
    rw [← L.map_comp,Enveloping.fiberInr_snd,L.map_zero]
  obtain ⟨v,hv₁,hv₂⟩ := StableFiberPair.exists_pair i p j
    hi he hj
    _ _ _ _ _ _ haz h₁₁ h₂₁ hj₁ h₁₂ h₂₂ hj₂
  refine ⟨v,?_,?_⟩
  · change v ≫ L.map (_ ≫ Enveloping.fiberFst u w Y) = _
    rw [L.map_comp,← Category.assoc]
    exact hv₁
  · change v ≫ L.map (_ ≫ Enveloping.fiberSnd u w Y) = _
    rw [L.map_comp,← Category.assoc]
    exact hv₂

end Evaluated

end
end TachikawaCharZero.StableFiberPair
