import TachikawaCharZero.TwoBranchCancellation
import TachikawaCharZero.EvaluatedCompleteLiftMap
import OAI.RingTheory.Tachikawa.GenericCompletePair

/-! Actual complete Hom of the rational difference fiber. The evaluated
short exact sequence and a projective covering summand give the genuine
two-projection comparison, rather than a dimension-only model. -/
namespace TachikawaCharZero.TwoBranchHom
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa
open ScalingSocle SocleBimodule FixedBimoduleY
open scoped ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

section Generic
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

theorem Hmap_factor (P : ChainComplex (ModuleCat R) ℤ) {A B C D : ModuleCat R}
    (i : A ⟶ B) (p : B ⟶ C) (e : C ⟶ D) (f : A ⟶ D)
    (hf : f = i ≫ p ≫ e) (a : ℤ) (x : VectorSplit.H (completeHom (k:=k) P A) a) :
    completeHmap (k:=k) P f a x =
      completeHmap P e a (completeHmap P p a (completeHmap P i a x)) := by
  rw [hf,completeHmap_comp,completeHmap_comp]
  rfl

end Generic

variable (H₁ H₂ : ℚ) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev middleComplex := completeHom (k:=ℚ) TateProfile.P
  (Enveloping.evalObj X (TwoBranchFiber.middle H₁ H₂ h₁ h₂))
abbrev inclusionMap := completeHomMap (k:=ℚ) TateProfile.P
  (Enveloping.evalMap X (TwoBranchFiber.inclusion H₁ H₂ h₁ h₂))
abbrev projectionMap := completeHomMap (k:=ℚ) TateProfile.P
  (Enveloping.evalMap X (TwoBranchFiber.projection H₁ H₂ h₁ h₂))

theorem shortExact :
    (∀ a, Function.Injective ((inclusionMap H₁ H₂ h₁ h₂).f a)) ∧
    (∀ a, Function.Exact ((inclusionMap H₁ H₂ h₁ h₂).f a)
      ((projectionMap H₁ H₂ h₁ h₂).f a)) ∧
    (∀ a, Function.Surjective ((projectionMap H₁ H₂ h₁ h₂).f a)) :=
  ⟨completeHomMap_injective _ _ (TwoBranchFiber.evaluated_injective H₁ H₂ h₁ h₂),
   completeHomMap_exact _ _ _ (TwoBranchFiber.evaluated_injective H₁ H₂ h₁ h₂)
    (TwoBranchFiber.evaluated_exact H₁ H₂ h₁ h₂),
   completeHomMap_surjective _ _ (TwoBranchFiber.evaluated_surjective H₁ H₂ h₁ h₂)
    (StableSeam.finiteX.complete_projective TateProfile.form)⟩

def rawPair (a : ℤ) :=
  (completeHmap (k:=ℚ) TateProfile.P (Enveloping.evalMap X
    (Enveloping.fiberFst (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y)) a).prod
  (completeHmap (k:=ℚ) TateProfile.P (Enveloping.evalMap X
    (Enveloping.fiberSnd (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y)) a)

theorem rawPair_bijective (a : ℤ) : Function.Bijective (rawPair H₁ H₂ h₁ h₂ a) := by
  let L := Enveloping.evaluation (k:=ℚ) (S:=E) X
  let U := TwoBranchFiber.U H₁ h₁
  let V := TwoBranchFiber.V H₂ h₂
  let Q := Enveloping.fiberCover Y
  let fQ : Module.Finite EE Q := by
    change Module.Finite EE (Fin Y.cover.rank → EE)
    infer_instance
  let projQ : Module.Projective EE Q := by
    change Module.Projective EE (Fin Y.cover.rank → EE)
    infer_instance
  let fEvalQ : Module.Finite E (L.obj Q) :=
    @Enveloping.evalFree_finite ℚ E E _ _ _ _ _ _ _ X _ Q fQ
  let : CategoryTheory.Projective Q := ModuleCat.projective_of_categoryTheory_projective _
  let : CategoryTheory.Projective (L.obj Q) := Enveloping.evaluation_projective X _
  let projEvalQ : Module.Projective E (L.obj Q) := ModuleCat.projective_of_module_projective _
  change Function.Bijective
    ((completeHmap (k:=ℚ) TateProfile.P (L.map (Enveloping.fiberFst U V Y)) a).prod
      (completeHmap TateProfile.P (L.map (Enveloping.fiberSnd U V Y)) a))
  apply @completeHpair_bijective ℚ E _ _ _ TateProfile.P
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    _ _ _ (L.obj Q) fEvalQ projEvalQ
    (L.map (Enveloping.fiberInl U V Y)) (L.map (Enveloping.fiberInm U V Y))
    (L.map (Enveloping.fiberInr U V Y)) _ _ (L.map (Enveloping.fiberThird U V Y))
  · rw [← L.map_comp,Enveloping.fiberInl_fst,L.map_id]
  · rw [← L.map_comp,Enveloping.fiberInl_snd,L.map_zero]
  · rw [← L.map_comp,Enveloping.fiberInm_fst,L.map_zero]
  · rw [← L.map_comp,Enveloping.fiberInm_snd,L.map_id]
  · rw [← L.map_comp,← L.map_comp,← L.map_comp,← L.map_add,← L.map_add,
      Enveloping.fiber_sum_id,L.map_id]

def targetIso (H : ℚ) (hH : H ≠ 0) :
    Enveloping.evalObj X (TwoBranchFiber.U H hH).obj ≅ X :=
  (Enveloping.evaluation (k:=ℚ) (S:=E) X).mapIso (TwoBranchAction.branchIso H hH) ≪≫
    Enveloping.twistedTensorIso (TensorTwistWeights.scale H hH) X ≪≫
      TensorTwistWeights.simpleIso H hH

def middlePair (a : ℤ) :=
  ((completeHomIso (k:=ℚ) TateProfile.P (targetIso H₁ h₁) a).prodCongr
    (completeHomIso (k:=ℚ) TateProfile.P (targetIso H₂ h₂) a)).toLinearMap.comp
      (rawPair H₁ H₂ h₁ h₂ a)

theorem middlePair_bijective (a : ℤ) : Function.Bijective (middlePair H₁ H₂ h₁ h₂ a) :=
  by
    dsimp only [middlePair,LinearMap.coe_comp,LinearEquiv.coe_coe]
    exact Function.Bijective.comp (LinearEquiv.bijective _)
      (rawPair_bijective H₁ H₂ h₁ h₂ a)

theorem firstTarget_factor : TwoBranchDelta.firstTarget H₁ H₂ h₁ h₂ =
    Enveloping.evalMap X (TwoBranchFiber.inclusion H₁ H₂ h₁ h₂) ≫
    Enveloping.evalMap X
      (Enveloping.fiberFst (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y) ≫
    (targetIso H₁ h₁).hom := by
  change (Enveloping.evaluation (k:=ℚ) (S:=E) X).map
    ((TwoBranchFiber.inclusion H₁ H₂ h₁ h₂ ≫
      Enveloping.fiberFst (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y) ≫
      (TwoBranchAction.branchIso H₁ h₁).hom) ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₁ h₁) X).hom ≫
      (TensorTwistWeights.simpleIso H₁ h₁).hom =
    (Enveloping.evaluation (k:=ℚ) (S:=E) X).map (TwoBranchFiber.inclusion H₁ H₂ h₁ h₂) ≫
    (Enveloping.evaluation (k:=ℚ) (S:=E) X).map
      (Enveloping.fiberFst (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y) ≫
    ((Enveloping.evaluation (k:=ℚ) (S:=E) X).map (TwoBranchAction.branchIso H₁ h₁).hom ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₁ h₁) X).hom ≫
      (TensorTwistWeights.simpleIso H₁ h₁).hom)
  simp only [Functor.map_comp,Category.assoc]

theorem secondTarget_factor : TwoBranchDelta.secondTarget H₁ H₂ h₁ h₂ =
    Enveloping.evalMap X (TwoBranchFiber.inclusion H₁ H₂ h₁ h₂) ≫
    Enveloping.evalMap X
      (Enveloping.fiberSnd (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y) ≫
    (targetIso H₂ h₂).hom := by
  change (Enveloping.evaluation (k:=ℚ) (S:=E) X).map
    ((TwoBranchFiber.inclusion H₁ H₂ h₁ h₂ ≫
      Enveloping.fiberSnd (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y) ≫
      (TwoBranchAction.branchIso H₂ h₂).hom) ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₂ h₂) X).hom ≫
      (TensorTwistWeights.simpleIso H₂ h₂).hom =
    (Enveloping.evaluation (k:=ℚ) (S:=E) X).map (TwoBranchFiber.inclusion H₁ H₂ h₁ h₂) ≫
    (Enveloping.evaluation (k:=ℚ) (S:=E) X).map
      (Enveloping.fiberSnd (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y) ≫
    ((Enveloping.evaluation (k:=ℚ) (S:=E) X).map (TwoBranchAction.branchIso H₂ h₂).hom ≫
      (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₂ h₂) X).hom ≫
      (TensorTwistWeights.simpleIso H₂ h₂).hom)
  simp only [Functor.map_comp,Category.assoc]

theorem pair_factor (a : ℤ) : TwoBranchDelta.pair H₁ H₂ h₁ h₂ a =
    (middlePair H₁ H₂ h₁ h₂ a).comp
      (VectorSplit.Hmap (inclusionMap H₁ H₂ h₁ h₂) a) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change completeHmap (k:=ℚ) TateProfile.P (TwoBranchDelta.firstTarget H₁ H₂ h₁ h₂) a x =
      completeHmap TateProfile.P (targetIso H₁ h₁).hom a
        (completeHmap TateProfile.P (Enveloping.evalMap X
          (Enveloping.fiberFst (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y)) a
          (completeHmap TateProfile.P (Enveloping.evalMap X
            (TwoBranchFiber.inclusion H₁ H₂ h₁ h₂)) a x))
    exact Hmap_factor TateProfile.P _ _ _ _ (firstTarget_factor H₁ H₂ h₁ h₂) a x
  · change completeHmap (k:=ℚ) TateProfile.P (TwoBranchDelta.secondTarget H₁ H₂ h₁ h₂) a x =
      completeHmap TateProfile.P (targetIso H₂ h₂).hom a
        (completeHmap TateProfile.P (Enveloping.evalMap X
          (Enveloping.fiberSnd (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y)) a
          (completeHmap TateProfile.P (Enveloping.evalMap X
            (TwoBranchFiber.inclusion H₁ H₂ h₁ h₂)) a x))
    exact Hmap_factor TateProfile.P _ _ _ _ (secondTarget_factor H₁ H₂ h₁ h₂) a x

theorem inclusion_injective (a : ℤ) (hm2 : a ≠ -2) (h1 : a ≠ 1) :
    Function.Injective (VectorSplit.Hmap (inclusionMap H₁ H₂ h₁ h₂) a) := by
  have hs := shortExact H₁ H₂ h₁ h₂
  exact VectorSplit.Hmap_injective_of_prev_zero _ _ hs.1 hs.2.1 hs.2.2 a
    (ReverseCorner.completeYHomology_zero (a-1) (by omega) (by omega))

theorem pair_injective_except (a : ℤ) (hm2 : a ≠ -2) (h1 : a ≠ 1) :
    Function.Injective (TwoBranchDelta.pair H₁ H₂ h₁ h₂ a) := by
  rw [pair_factor]
  exact (middlePair_bijective H₁ H₂ h₁ h₂ a).1.comp
    (inclusion_injective H₁ H₂ h₁ h₂ a hm2 h1)

def firstInjection : X ⟶ Enveloping.evalObj X (TwoBranchFiber.middle H₁ H₂ h₁ h₂) :=
  (FixedYEvaluation.uXIso H₁ h₁).inv ≫ Enveloping.evalMap X
    (Enveloping.fiberInl (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y)

theorem firstInjection_projection : firstInjection H₁ H₂ h₁ h₂ ≫
    Enveloping.evalMap X (TwoBranchFiber.projection H₁ H₂ h₁ h₂) =
      EvaluatedLiftNormalization.evaluatedLift H₁ h₁ := by
  let L := Enveloping.evaluation (k:=ℚ) (S:=E) X
  change ((FixedYEvaluation.uXIso H₁ h₁).inv ≫ L.map
    (Enveloping.fiberInl (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y)) ≫
    L.map (TwoBranchFiber.projection H₁ H₂ h₁ h₂) = _
  exact (Category.assoc _ _ _).trans (congrArg (fun f =>
    (FixedYEvaluation.uXIso H₁ h₁).inv ≫ f) ((L.map_comp _ _).symm.trans
      (congrArg L.map (Enveloping.fiberInl_projection
        (TwoBranchFiber.U H₁ h₁) (TwoBranchFiber.V H₂ h₂) Y
        (EvaluatedLiftNormalization.lift H₁ h₁) (-EvaluatedLiftNormalization.lift H₂ h₂)))))

theorem projection_zero_surjective : Function.Surjective
    (VectorSplit.Hmap (projectionMap H₁ H₂ h₁ h₂) 0) := by
  have he : (VectorSplit.Hmap (projectionMap H₁ H₂ h₁ h₂) 0).comp
      (completeHmap (k:=ℚ) TateProfile.P (firstInjection H₁ H₂ h₁ h₂) 0) =
      EvaluatedCompleteLiftMap.inducedMap H₁ h₁ 0 :=
    (completeHmap_comp (k:=ℚ) TateProfile.P _ _ 0).symm.trans
      (congrArg (fun f => completeHmap (k:=ℚ) TateProfile.P f 0)
        (firstInjection_projection H₁ H₂ h₁ h₂))
  intro y
  obtain ⟨x,hx⟩ := (EvaluatedCompleteLiftMap.inducedMap_zero_bijective H₁ h₁).2 y
  exact ⟨completeHmap (k:=ℚ) TateProfile.P (firstInjection H₁ H₂ h₁ h₂) 0 x,
    (LinearMap.congr_fun he x).trans hx⟩

theorem inclusion_one_injective : Function.Injective
    (VectorSplit.Hmap (inclusionMap H₁ H₂ h₁ h₂) 1) := by
  have hs := shortExact H₁ H₂ h₁ h₂
  exact VectorSplit.Hmap_injective_of_prev_surjective _ _ hs.1 hs.2.1 hs.2.2 1
    (by simpa using projection_zero_surjective H₁ H₂ h₁ h₂)

theorem pair_injective (a : ℤ) (hm2 : a ≠ -2) :
    Function.Injective (TwoBranchDelta.pair H₁ H₂ h₁ h₂ a) := by
  by_cases h1 : a = 1
  · subst a
    rw [pair_factor]
    exact (middlePair_bijective H₁ H₂ h₁ h₂ 1).1.comp
      (inclusion_one_injective H₁ H₂ h₁ h₂)
  · exact pair_injective_except H₁ H₂ h₁ h₂ a hm2 h1

theorem VAction_injective (a : ℤ) : Function.Injective
    (VectorSplit.Hmap (TwoBranchDelta.VAction H₁ H₂ h₁ h₂) a) := by
  intro x y h
  exact (TwoBranchDelta.VAction_first_H H₁ H₂ h₁ h₂ a x).symm.trans
    ((congrArg (VectorSplit.Hmap (TwoBranchDelta.firstProjection H₁ H₂ h₁ h₂) a) h).trans
      (TwoBranchDelta.VAction_first_H H₁ H₂ h₁ h₂ a y))

theorem VAction_zero_surjective : Function.Surjective
    (VectorSplit.Hmap (TwoBranchDelta.VAction H₁ H₂ h₁ h₂) 0) := by
  let em := (LinearEquiv.ofBijective (middlePair H₁ H₂ h₁ h₂ 0)
    (middlePair_bijective H₁ H₂ h₁ h₂ 0)).trans
      (TateProfile.zeroEquiv.prodCongr TateProfile.zeroEquiv)
  have hs := shortExact H₁ H₂ h₁ h₂
  exact exact_line_surjective
    (VectorSplit.Hmap (inclusionMap H₁ H₂ h₁ h₂) 0)
    (VectorSplit.Hmap (projectionMap H₁ H₂ h₁ h₂) 0)
    (inclusion_injective H₁ H₂ h₁ h₂ 0 (by decide) (by decide))
    (projection_zero_surjective H₁ H₂ h₁ h₂)
    (VectorSplit.Hmap_exact _ _ hs.1 hs.2.1 hs.2.2 0)
    em ReverseCorner.completeYZeroEquiv TateProfile.zeroEquiv _
    (VAction_injective H₁ H₂ h₁ h₂ 0)

def zeroEquiv : VectorSplit.H (TwoBranchDelta.fiberComplex H₁ H₂ h₁ h₂) 0 ≃ₗ[ℚ] ℚ :=
  (LinearEquiv.ofBijective (VectorSplit.Hmap (TwoBranchDelta.VAction H₁ H₂ h₁ h₂) 0)
    ⟨VAction_injective H₁ H₂ h₁ h₂ 0,VAction_zero_surjective H₁ H₂ h₁ h₂⟩).symm.trans
      TateProfile.zeroEquiv

theorem zero_finrank : Module.finrank ℚ
    (VectorSplit.H (TwoBranchDelta.fiberComplex H₁ H₂ h₁ h₂) 0) = 1 := by
  rw [(zeroEquiv H₁ H₂ h₁ h₂).finrank_eq]
  simp

theorem delta_zero_surjective (ε : ℚ) (hε : ε ≠ 0) :
    Function.Surjective (TwoBranchDelta.delta H₁ H₂ h₁ h₂ ε 0) := by
  intro x
  obtain ⟨y,hy⟩ := VAction_zero_surjective H₁ H₂ h₁ h₂ x
  refine ⟨(0,-(ε⁻¹ • y)),?_⟩
  rw [TwoBranchDelta.delta_apply,map_zero,map_neg,map_smul,smul_neg,
    smul_smul,mul_inv_cancel₀ hε,one_smul,hy]
  simp

end
end TachikawaCharZero.TwoBranchHom
