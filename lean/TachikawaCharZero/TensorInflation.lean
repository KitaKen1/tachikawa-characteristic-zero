import TachikawaCharZero.SplitInflation

/-! Exact tensoring with the one-dimensional character is naturally
isomorphic to split inflation. This identifies the actual Yoneda axes
with maps induced by the outer tensor bifunctor, with no choice of
Künneth coordinates. Cross-factor shifted interchange remains separate. -/
namespace TachikawaCharZero.TensorInflation
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Induced TensorProfile SplitInflation OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

abbrev tensorLeft := (OuterTensor.bifunctor ℚ T T).flip.obj X
abbrev tensorRight := (OuterTensor.bifunctor ℚ T T).obj X

def leftUnderlying (M : ModuleCat T) : tensorLeft.obj M ≃ₗ[ℚ] (M ⊗[ℚ] sCanon) :=
  OuterTensor.underlyingEquiv M sCanon
def rightUnderlying (M : ModuleCat T) : tensorRight.obj M ≃ₗ[ℚ] (sCanon ⊗[ℚ] M) :=
  OuterTensor.underlyingEquiv sCanon M

def leftPure (M : ModuleCat T) (x : M) (y : sCanon) : tensorLeft.obj M :=
  (leftUnderlying M).symm (x ⊗ₜ[ℚ] y)
def rightPure (M : ModuleCat T) (x : sCanon) (y : M) : tensorRight.obj M :=
  (rightUnderlying M).symm (x ⊗ₜ[ℚ] y)

def leftGround (M : ModuleCat T) : tensorLeft.obj M ≃ₗ[ℚ] M :=
  (leftUnderlying M).trans
    ((TensorProduct.congr (LinearEquiv.refl ℚ M) simpleGroundEquiv).trans
      (TensorProduct.rid ℚ M))
def rightGround (M : ModuleCat T) : tensorRight.obj M ≃ₗ[ℚ] M :=
  (rightUnderlying M).trans
    ((TensorProduct.congr simpleGroundEquiv (LinearEquiv.refl ℚ M)).trans
      (TensorProduct.lid ℚ M))

theorem leftGround_pure (M : ModuleCat T) (x : M) (y : sCanon) :
    leftGround M (leftPure M x y) = (show ℚ from y) • x := by
  change (TensorProduct.rid ℚ M)
    (TensorProduct.map (LinearMap.id : M →ₗ[ℚ] M) simpleGroundEquiv.toLinearMap
      (x ⊗ₜ[ℚ] y)) = _
  rw [TensorProduct.map_tmul, TensorProduct.rid_tmul]
  rfl

theorem rightGround_pure (M : ModuleCat T) (x : sCanon) (y : M) :
    rightGround M (rightPure M x y) = (show ℚ from x) • y := by
  change (TensorProduct.lid ℚ M)
    (TensorProduct.map simpleGroundEquiv.toLinearMap (LinearMap.id : M →ₗ[ℚ] M)
      (x ⊗ₜ[ℚ] y)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
  rfl

theorem leftPure_action (M : ModuleCat T) (a b : T) (x : M) (y : sCanon) :
    (a ⊗ₜ[ℚ] b) • leftPure M x y = leftPure M (a • x) (b • y) :=
  OuterTensor.tmul_smul_tmul ℚ T T M sCanon a b x y
theorem rightPure_action (M : ModuleCat T) (a b : T) (x : sCanon) (y : M) :
    (a ⊗ₜ[ℚ] b) • rightPure M x y = rightPure M (a • x) (b • y) :=
  OuterTensor.tmul_smul_tmul ℚ T T sCanon M a b x y

theorem leftGround_action (M : ModuleCat T) (r : E) (z : tensorLeft.obj M) :
    leftGround M (r • z) = projectionLeft r • leftGround M z := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp [add_smul, hr, hs]
  | tmul a b =>
    obtain ⟨w,rfl⟩ := (leftUnderlying M).symm.surjective z
    induction w using TensorProduct.inductionOn with
    | add x y hx hy =>
      have hadd : (a ⊗ₜ[ℚ] b) • (leftUnderlying M).symm (x+y) =
          (a ⊗ₜ[ℚ] b) • (leftUnderlying M).symm x +
            (a ⊗ₜ[ℚ] b) • (leftUnderlying M).symm y :=
        (OuterTensor.action ℚ T T M sCanon (a ⊗ₜ[ℚ] b)).map_add x y
      rw [hadd, map_add, map_add, map_add, smul_add, hx, hy]
    | tmul x y =>
      change leftGround M ((a ⊗ₜ[ℚ] b) • leftPure M x y) =
        projectionLeft (a ⊗ₜ[ℚ] b) • leftGround M (leftPure M x y)
      rw [leftPure_action, leftGround_pure, leftGround_pure, projectionLeft_tmul]
      change (characterT b * (show ℚ from y)) • (a • x) =
        (characterT b • a) • ((show ℚ from y) • x)
      rw [mul_smul, smul_assoc, smul_comm a (show ℚ from y)]

theorem rightGround_action (M : ModuleCat T) (r : E) (z : tensorRight.obj M) :
    rightGround M (r • z) = projectionRight r • rightGround M z := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp [add_smul, hr, hs]
  | tmul a b =>
    obtain ⟨w,rfl⟩ := (rightUnderlying M).symm.surjective z
    induction w using TensorProduct.inductionOn with
    | add x y hx hy =>
      have hadd : (a ⊗ₜ[ℚ] b) • (rightUnderlying M).symm (x+y) =
          (a ⊗ₜ[ℚ] b) • (rightUnderlying M).symm x +
            (a ⊗ₜ[ℚ] b) • (rightUnderlying M).symm y :=
        (OuterTensor.action ℚ T T sCanon M (a ⊗ₜ[ℚ] b)).map_add x y
      rw [hadd, map_add, map_add, map_add, smul_add, hx, hy]
    | tmul x y =>
      change rightGround M ((a ⊗ₜ[ℚ] b) • rightPure M x y) =
        projectionRight (a ⊗ₜ[ℚ] b) • rightGround M (rightPure M x y)
      rw [rightPure_action, rightGround_pure, rightGround_pure, projectionRight_tmul]
      change (characterT a * (show ℚ from x)) • (b • y) =
        (characterT a • b) • ((show ℚ from x) • y)
      rw [mul_smul, smul_assoc, smul_comm b (show ℚ from x)]

def leftIso (M : ModuleCat T) : tensorLeft.obj M ≅ inflateLeft.obj M :=
  (show tensorLeft.obj M ≃ₗ[E] inflateLeft.obj M from
    { __ := (leftGround M).toAddEquiv
      map_smul' := leftGround_action M }).toModuleIso
def rightIso (M : ModuleCat T) : tensorRight.obj M ≅ inflateRight.obj M :=
  (show tensorRight.obj M ≃ₗ[E] inflateRight.obj M from
    { __ := (rightGround M).toAddEquiv
      map_smul' := rightGround_action M }).toModuleIso

theorem leftPure_map {M N : ModuleCat T} (f : M ⟶ N) (x : M) (y : sCanon) :
    tensorLeft.map f (leftPure M x y) = leftPure N (f x) y := rfl
theorem rightPure_map {M N : ModuleCat T} (f : M ⟶ N) (x : sCanon) (y : M) :
    tensorRight.map f (rightPure M x y) = rightPure N x (f y) := rfl

def leftNatIso : tensorLeft ≅ inflateLeft := NatIso.ofComponents leftIso (by
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change leftGround N (tensorLeft.map f z) = f (leftGround M z)
  obtain ⟨w,rfl⟩ := (leftUnderlying M).symm.surjective z
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    change leftGround N (tensorLeft.map f (leftPure M x y)) = f (leftGround M (leftPure M x y))
    rw [leftPure_map, leftGround_pure, leftGround_pure]
    exact (f.hom.map_smul_of_tower (show ℚ from y) x).symm)

def rightNatIso : tensorRight ≅ inflateRight := NatIso.ofComponents rightIso (by
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change rightGround N (tensorRight.map f z) = f (rightGround M z)
  obtain ⟨w,rfl⟩ := (rightUnderlying M).symm.surjective z
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    change rightGround N (tensorRight.map f (rightPure M x y)) = f (rightGround M (rightPure M x y))
    rw [rightPure_map, rightGround_pure, rightGround_pure]
    exact (f.hom.map_smul_of_tower (show ℚ from x) y).symm)

instance : tensorLeft.Additive := CategoryTheory.Functor.additive_of_iso leftNatIso.symm
instance : tensorLeft.Linear ℚ := CategoryTheory.Functor.linear_of_iso ℚ leftNatIso.symm
instance : PreservesFiniteLimits tensorLeft := preservesFiniteLimits_of_natIso leftNatIso.symm
instance : PreservesFiniteColimits tensorLeft := preservesFiniteColimits_of_natIso leftNatIso.symm
instance : PreservesFiniteLimits tensorRight := preservesFiniteLimits_of_natIso rightNatIso.symm
instance : PreservesFiniteColimits tensorRight := preservesFiniteColimits_of_natIso rightNatIso.symm
instance : tensorRight.Linear ℚ := CategoryTheory.Functor.linear_of_iso ℚ rightNatIso.symm

theorem leftIso_at_character : leftIso X = inflatedLeftIso.symm := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change leftGround X z = (show S from groundEquiv z)
  apply simpleGroundEquiv.injective
  change simpleGroundEquiv (leftGround X z) = groundEquiv z
  obtain ⟨w,rfl⟩ := (leftUnderlying X).symm.surjective z
  induction w using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add]
    erw [map_add, hx, hy]
  | tmul x y =>
    change simpleGroundEquiv (leftGround X (leftPure X x y)) =
      groundEquiv (pureTensor x y)
    refine (congrArg simpleGroundEquiv (leftGround_pure X x y)).trans ?_
    refine (simpleGroundEquiv.map_smul (show ℚ from y) (show sCanon from x)).trans ?_
    change (show ℚ from y) * (show ℚ from x) = groundEquiv (pureTensor x y)
    exact (mul_comm (show ℚ from y) (show ℚ from x)).trans
      (groundEquiv_tmul (show sCanon from x) y).symm

theorem rightIso_at_character : rightIso X = inflatedRightIso.symm := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change rightGround X z = (show S from groundEquiv z)
  apply simpleGroundEquiv.injective
  change simpleGroundEquiv (rightGround X z) = groundEquiv z
  obtain ⟨w,rfl⟩ := (rightUnderlying X).symm.surjective z
  induction w using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add]
    erw [map_add, hx, hy]
  | tmul x y =>
    change simpleGroundEquiv (rightGround X (rightPure X x y)) =
      groundEquiv (pureTensor x y)
    refine (congrArg simpleGroundEquiv (rightGround_pure X x y)).trans ?_
    refine (simpleGroundEquiv.map_smul (show ℚ from x) (show sCanon from y)).trans ?_
    change (show ℚ from x) * (show ℚ from y) = groundEquiv (pureTensor x y)
    exact (groundEquiv_tmul x (show sCanon from y)).symm

theorem tensorLeft_map_ext {n : ℕ} (x : Ext X X n) :
    x.mapExactFunctor tensorLeft = externalLeft n x := by
  have h := ExtTransport.conjugate_map_natIso inflateLeft leftNatIso.symm x
  change ExtTransport.conjugate (leftIso X).symm (x.mapExactFunctor inflateLeft) = _ at h
  rw [leftIso_at_character] at h
  exact h.symm

theorem tensorRight_map_ext {n : ℕ} (x : Ext X X n) :
    x.mapExactFunctor tensorRight = externalRight n x := by
  have h := ExtTransport.conjugate_map_natIso inflateRight rightNatIso.symm x
  change ExtTransport.conjugate (rightIso X).symm (x.mapExactFunctor inflateRight) = _ at h
  rw [rightIso_at_character] at h
  exact h.symm

theorem leftPower_eq_tensor (m : ℕ) :
    leftPower m = (tauPower m).mapExactFunctor tensorLeft :=
  (tensorLeft_map_ext (tauPower m)).symm

theorem rightPower_eq_tensor (m : ℕ) :
    rightPower m = (tauPower m).mapExactFunctor tensorRight :=
  (tensorRight_map_ext (tauPower m)).symm

theorem alpha_eq_tensor_tau : alpha = tau.mapExactFunctor tensorLeft := by
  rw [alpha_eq_inflated_tau, ← tensorLeft_map_ext]

theorem beta_eq_tensor_tau : beta = tau.mapExactFunctor tensorRight := by
  rw [beta_eq_inflated_tau, ← tensorRight_map_ext]

end
end TachikawaCharZero.TensorInflation
