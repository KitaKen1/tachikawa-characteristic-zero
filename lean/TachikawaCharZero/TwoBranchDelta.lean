import TachikawaCharZero.TwoBranchAction

/-! The actual complete tensor action and target action give a signed Delta.
Its actual two projections are the scalar block formula. Bijectivity of
the projection pair, the F-Hom profile and the cone comparison remain separate. -/
namespace TachikawaCharZero.TwoBranchDelta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open CategoryTheory OAI.Tachikawa ScalingSocle SocleBimodule
open scoped ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

section Generic
variable {C : Type*} [Category C] {A B U V : C}

theorem cancel_inverses (v : A ⟶ B) (p : B ⟶ U) (t : U ≅ V) (e : V ≅ A)
    (h : v ≫ p = e.inv ≫ t.inv) : v ≫ (p ≫ t.hom ≫ e.hom) = 𝟙 A := by
  rw [← Category.assoc,← Category.assoc,h]
  simp only [Category.assoc,Iso.inv_hom_id,Category.id_comp]

end Generic

variable (H₁ H₂ : ℚ) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev selfComplex := completeHom (k:=ℚ) TateProfile.P X
abbrev fiberComplex := completeHom (k:=ℚ) TateProfile.P
  (Enveloping.evalObj X (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj)

def firstTarget : Enveloping.evalObj X (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj ⟶ X :=
  Enveloping.evalMap X (TwoBranchAction.first H₁ H₂ h₁ h₂) ≫
    (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₁ h₁) X).hom ≫
    (TensorTwistWeights.simpleIso H₁ h₁).hom
def secondTarget : Enveloping.evalObj X (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj ⟶ X :=
  Enveloping.evalMap X (TwoBranchAction.second H₁ H₂ h₁ h₂) ≫
    (Enveloping.twistedTensorIso (TensorTwistWeights.scale H₂ h₂) X).hom ≫
    (TensorTwistWeights.simpleIso H₂ h₂).hom

theorem v_first : TwoBranchFiber.vZero H₁ H₂ h₁ h₂ ≫
    firstTarget H₁ H₂ h₁ h₂ = 𝟙 X :=
  cancel_inverses _ _ _ _ (TwoBranchAction.vZero_first H₁ H₂ h₁ h₂)
theorem v_second : TwoBranchFiber.vZero H₁ H₂ h₁ h₂ ≫
    secondTarget H₁ H₂ h₁ h₂ = 𝟙 X :=
  cancel_inverses _ _ _ _ (TwoBranchAction.vZero_second H₁ H₂ h₁ h₂)

def FAction : selfComplex ⟶ fiberComplex H₁ H₂ h₁ h₂ :=
  completeFunctorHom (k:=ℚ) (Enveloping.tensorFunctor (TwoBranchFiber.F H₁ H₂ h₁ h₂).obj)
    TateProfile.P TateProfile.P X (TwoBranchAction.completeLift H₁ H₂ h₁ h₂)
def VAction : selfComplex ⟶ fiberComplex H₁ H₂ h₁ h₂ :=
  completeHomMap TateProfile.P (TwoBranchFiber.vZero H₁ H₂ h₁ h₂)
def firstProjection : fiberComplex H₁ H₂ h₁ h₂ ⟶ selfComplex :=
  completeHomMap TateProfile.P (firstTarget H₁ H₂ h₁ h₂)
def secondProjection : fiberComplex H₁ H₂ h₁ h₂ ⟶ selfComplex :=
  completeHomMap TateProfile.P (secondTarget H₁ H₂ h₁ h₂)

theorem VAction_first : VAction H₁ H₂ h₁ h₂ ≫ firstProjection H₁ H₂ h₁ h₂ = 𝟙 selfComplex :=
  (completeHomMap_comp (k:=ℚ) TateProfile.P _ _).symm.trans
    ((congrArg (completeHomMap (k:=ℚ) TateProfile.P) (v_first H₁ H₂ h₁ h₂)).trans
      (completeHomMap_id (k:=ℚ) TateProfile.P))
theorem VAction_second : VAction H₁ H₂ h₁ h₂ ≫ secondProjection H₁ H₂ h₁ h₂ = 𝟙 selfComplex :=
  (completeHomMap_comp (k:=ℚ) TateProfile.P _ _).symm.trans
    ((congrArg (completeHomMap (k:=ℚ) TateProfile.P) (v_second H₁ H₂ h₁ h₂)).trans
      (completeHomMap_id (k:=ℚ) TateProfile.P))

theorem FAction_first (a : ℤ) (x : TateProfile.Tate a) :
    VectorSplit.Hmap (firstProjection H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (FAction H₁ H₂ h₁ h₂) a x) =
        TwistedBranchWeights.weight H₁ a • x :=
  (LinearMap.congr_fun (VectorSplit.Hmap_comp _ _ a) x).symm.trans
    (TwoBranchAction.first_weight H₁ H₂ h₁ h₂ a x)
theorem FAction_second (a : ℤ) (x : TateProfile.Tate a) :
    VectorSplit.Hmap (secondProjection H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (FAction H₁ H₂ h₁ h₂) a x) =
        TwistedBranchWeights.weight H₂ a • x :=
  (LinearMap.congr_fun (VectorSplit.Hmap_comp _ _ a) x).symm.trans
    (TwoBranchAction.second_weight H₁ H₂ h₁ h₂ a x)

theorem VAction_first_H (a : ℤ) (x : TateProfile.Tate a) :
    VectorSplit.Hmap (firstProjection H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (VAction H₁ H₂ h₁ h₂) a x) = x := by
  have h := (VectorSplit.Hmap_comp (VAction H₁ H₂ h₁ h₂)
    (firstProjection H₁ H₂ h₁ h₂) a).symm.trans
    ((congrArg (fun f => VectorSplit.Hmap f a) (VAction_first H₁ H₂ h₁ h₂)).trans
      (VectorSplit.Hmap_id a))
  exact LinearMap.congr_fun h x
theorem VAction_second_H (a : ℤ) (x : TateProfile.Tate a) :
    VectorSplit.Hmap (secondProjection H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (VAction H₁ H₂ h₁ h₂) a x) = x := by
  have h := (VectorSplit.Hmap_comp (VAction H₁ H₂ h₁ h₂)
    (secondProjection H₁ H₂ h₁ h₂) a).symm.trans
    ((congrArg (fun f => VectorSplit.Hmap f a) (VAction_second H₁ H₂ h₁ h₂)).trans
      (VectorSplit.Hmap_id a))
  exact LinearMap.congr_fun h x

def delta (ε : ℚ) (a : ℤ) : (TateProfile.Tate a × TateProfile.Tate a) →ₗ[ℚ]
    VectorSplit.H (fiberComplex H₁ H₂ h₁ h₂) a :=
  (VectorSplit.Hmap (FAction H₁ H₂ h₁ h₂) a).comp (LinearMap.fst ℚ _ _) -
    ε • (VectorSplit.Hmap (VAction H₁ H₂ h₁ h₂) a).comp (LinearMap.snd ℚ _ _)

theorem delta_apply (ε : ℚ) (a : ℤ) (x y : TateProfile.Tate a) :
    delta H₁ H₂ h₁ h₂ ε a (x,y) = VectorSplit.Hmap (FAction H₁ H₂ h₁ h₂) a x -
      ε • VectorSplit.Hmap (VAction H₁ H₂ h₁ h₂) a y := rfl

theorem projected_first (ε : ℚ) (a : ℤ) (x y : TateProfile.Tate a) :
    VectorSplit.Hmap (firstProjection H₁ H₂ h₁ h₂) a
      (delta H₁ H₂ h₁ h₂ ε a (x,y)) = TwistedBranchWeights.weight H₁ a • x - ε • y := by
  rw [delta_apply,map_sub,map_smul,FAction_first,VAction_first_H]

theorem projected_second (ε : ℚ) (a : ℤ) (x y : TateProfile.Tate a) :
    VectorSplit.Hmap (secondProjection H₁ H₂ h₁ h₂) a
      (delta H₁ H₂ h₁ h₂ ε a (x,y)) = TwistedBranchWeights.weight H₂ a • x - ε • y := by
  rw [delta_apply,map_sub,map_smul,FAction_second,VAction_second_H]

def pair (a : ℤ) : VectorSplit.H (fiberComplex H₁ H₂ h₁ h₂) a →ₗ[ℚ]
    (TateProfile.Tate a × TateProfile.Tate a) :=
  (VectorSplit.Hmap (firstProjection H₁ H₂ h₁ h₂) a).prod
    (VectorSplit.Hmap (secondProjection H₁ H₂ h₁ h₂) a)

theorem pair_delta (ε : ℚ) (a : ℤ) (x y : TateProfile.Tate a) :
    pair H₁ H₂ h₁ h₂ a (delta H₁ H₂ h₁ h₂ ε a (x,y)) =
      (TwistedBranchWeights.weight H₁ a • x - ε • y,
       TwistedBranchWeights.weight H₂ a • x - ε • y) :=
  Prod.ext (projected_first H₁ H₂ h₁ h₂ ε a x y) (projected_second H₁ H₂ h₁ h₂ ε a x y)

end
end TachikawaCharZero.TwoBranchDelta
