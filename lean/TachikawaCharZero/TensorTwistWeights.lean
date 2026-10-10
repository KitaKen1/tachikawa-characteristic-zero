import TachikawaCharZero.SimpleTwistWeights
import TachikawaCharZero.MonomialBasis
import TachikawaCharZero.SocleBimodule

/-! Actual ordinary Ext weights for the tensor scaling. Split inflation
commutes with the scaling restriction, up to an identity natural isomorphism.
This avoids rebuilding a tensor resolution or choosing Kunneth coordinates:
the checked Yoneda monomial basis carries the common scalar weight. -/
namespace TachikawaCharZero.TensorTwistWeights
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Abelian OAI.Tachikawa
open TensorProfile SplitInflation MonomialBasis
open scoped TensorProduct ModuleCat.Algebra

variable (H : ℚ) (hH : H ≠ 0)

def scale : E ≃ₐ[ℚ] E := Algebra.TensorProduct.congr
  (SimpleTwistWeights.scale H hH) (SimpleTwistWeights.scale H hH)
abbrev twist := SymmetrizingForm.twistFunctor (scale H hH)

instance : (twist H hH).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (scale H hH).symm.toRingEquiv

theorem projection_natural (π : E →ₐ[ℚ] Induced.T)
    (hπ : π=projectionLeft ∨ π=projectionRight) (r : E) :
    π (scale H hH r) = SimpleTwistWeights.scale H hH (π r) := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [map_add,hr,hs]
  | tmul a b =>
    rcases hπ with rfl | rfl
    · change projectionLeft
        (SimpleTwistWeights.scale H hH a ⊗ₜ[ℚ] SimpleTwistWeights.scale H hH b) = _
      rw [projectionLeft_tmul,projectionLeft_tmul,map_smul]
      rfl
    · change projectionRight
        (SimpleTwistWeights.scale H hH a ⊗ₜ[ℚ] SimpleTwistWeights.scale H hH b) = _
      rw [projectionRight_tmul,projectionRight_tmul,map_smul]
      rfl

theorem projection_inverse (π : E →ₐ[ℚ] Induced.T)
    (hπ : π=projectionLeft ∨ π=projectionRight) (r : E) :
    π ((scale H hH).symm r) = (SimpleTwistWeights.scale H hH).symm (π r) := by
  apply (SimpleTwistWeights.scale H hH).injective
  rw [← projection_natural H hH π hπ,AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

def inflationSquare (π : E →ₐ[ℚ] Induced.T)
    (hπ : π=projectionLeft ∨ π=projectionRight) :
    AlgebraInduction.res π ⋙ twist H hH ≅
      SimpleTwistWeights.twist H hH ⋙ AlgebraInduction.res π :=
  (ModuleCat.restrictScalarsComp (scale H hH).symm.toRingHom π.toRingHom).symm ≪≫
    ModuleCat.restrictScalarsComp' π.toRingHom
      (SimpleTwistWeights.scale H hH).symm.toRingHom
      (π.toRingHom.comp (scale H hH).symm.toRingHom)
      (by
        apply RingHom.ext
        intro r
        exact projection_inverse H hH π hπ r)

theorem character_scale (r : E) : tensorCharacter (scale H hH r)=tensorCharacter r := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [map_add,hr,hs]
  | tmul a b =>
    change tensorCharacter
      (SimpleTwistWeights.scale H hH a ⊗ₜ[ℚ] SimpleTwistWeights.scale H hH b)=_
    rw [tensorCharacter_tmul,tensorCharacter_tmul]
    rfl

theorem character_inverse (r : E) : tensorCharacter ((scale H hH).symm r)=tensorCharacter r := by
  have h := character_scale H hH ((scale H hH).symm r)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

def simpleIso : (twist H hH).obj X₂ ≅ X₂ where
  hom := ModuleCat.ofHom (X := (twist H hH).obj X₂) (Y := X₂)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' r x := by
        apply groundEquiv.injective
        change groundEquiv ((scale H hH).symm r • (show X₂ from x)) =
          groundEquiv (r • (show X₂ from x))
        rw [groundEquiv_action,groundEquiv_action,character_inverse] }
  inv := ModuleCat.ofHom (X := X₂) (Y := (twist H hH).obj X₂)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' r x := by
        apply groundEquiv.injective
        change groundEquiv (r • x) = groundEquiv ((scale H hH).symm r • x)
        rw [groundEquiv_action,groundEquiv_action,character_inverse] }
  hom_inv_id := rfl
  inv_hom_id := rfl

def action (n : ℕ) : Ext X₂ X₂ n →ₗ[ℚ] Ext X₂ X₂ n :=
  (ExtTransport.conjugateLinearMap ℚ (simpleIso H hH) n).comp
    ((twist H hH).mapExtLinearMap ℚ X₂ X₂ n)

theorem conjugate_trans {R : Type} [Ring R] {A B C : ModuleCat R}
    (e : A ≅ B) (f : B ≅ C) {n : ℕ} (x : Ext A A n) :
    ExtTransport.conjugate f (ExtTransport.conjugate e x) =
      ExtTransport.conjugate (e ≪≫ f) x := by
  simp only [ExtTransport.conjugate,Iso.trans_inv,Iso.trans_hom,
    ← Ext.comp_assoc_of_third_deg_zero,Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀_assoc,Ext.mk₀_comp_mk₀]

theorem action_external (π : E →ₐ[ℚ] Induced.T)
    (hπ : π=projectionLeft ∨ π=projectionRight)
    (hχ : Induced.characterT.comp π=tensorCharacter) (n : ℕ) (x : Ext Induced.X Induced.X n) :
    action H hH n (externalMap π hχ n x) =
      externalMap π hχ n (SimpleTwistWeights.action H hH n x) := by
  let I := AlgebraInduction.res π
  let e := inflatedIso π hχ
  let s := inflationSquare H hH π hπ
  have he : (twist H hH).mapIso e ≪≫ simpleIso H hH =
      s.app Induced.X ≪≫ I.mapIso (SimpleTwistWeights.simpleIso H hH) ≪≫ e := by
    apply Iso.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  change ExtTransport.conjugate _ ((ExtTransport.conjugate e (x.mapExactFunctor I)).mapExactFunctor _) =
    ExtTransport.conjugate e ((ExtTransport.conjugate _ (x.mapExactFunctor _)).mapExactFunctor I)
  rw [ExtTransport.map_conjugate,ExtTransport.map_conjugate,
    conjugate_trans,conjugate_trans,he,← conjugate_trans,← conjugate_trans]
  rw [← Ext.comp_mapExactFunctor,ExtTransport.conjugate_map_natIso,
    Ext.comp_mapExactFunctor]
  rw [conjugate_trans]

theorem action_comp {a b c : ℕ} (x : Ext X₂ X₂ a) (y : Ext X₂ X₂ b) (h : a+b=c) :
    action H hH c (x.comp y h) =
      (action H hH a x).comp (action H hH b y) h := by
  change ExtTransport.conjugate _ ((x.comp y h).mapExactFunctor _) = _
  rw [Ext.mapExactFunctor_comp,ExtTransport.conjugate_comp]
  rfl

theorem action_leftPower (m : ℕ) :
    action H hH (3*m) (leftPower m) = (H⁻¹)^m • leftPower m := by
  rw [leftPower,action_external H hH projectionLeft (Or.inl rfl),
    SimpleTwistWeights.action_tauPower H hH,map_smul]

theorem action_rightPower (m : ℕ) :
    action H hH (3*m) (rightPower m) = (H⁻¹)^m • rightPower m := by
  rw [rightPower,action_external H hH projectionRight (Or.inr rfl),
    SimpleTwistWeights.action_tauPower H hH,map_smul]

theorem action_monomials (m : ℕ) (i : Fin (m+1)) :
    action H hH (3*m) (monomials m i) = (H⁻¹)^m • monomials m i := by
  rw [monomials_eq_product,action_comp,action_leftPower,action_rightPower,
    Ext.smul_comp,Ext.comp_smul,smul_smul,← pow_add]
  rw [show i.val+(m-i.val)=m by omega]

theorem action_multiple (m : ℕ) (x : Ext X₂ X₂ (3*m)) :
    action H hH (3*m) x = (H⁻¹)^m • x := by
  nth_rw 1 [monomial_expansion m x]
  rw [map_sum]
  simp only [map_smul,action_monomials,smul_comm (_ : ℚ) ((H⁻¹)^m)]
  rw [← Finset.smul_sum,← monomial_expansion]

theorem action_all (n : ℕ) (x : Ext X₂ X₂ n) :
    action H hH n x = (H⁻¹)^(n/3) • x := by
  by_cases hn : n%3=0
  · obtain ⟨m,rfl⟩ := Nat.dvd_of_mod_eq_zero hn
    simpa only [Nat.mul_div_cancel_left m (by omega : 0<3)] using action_multiple H hH m x
  · let := TensorProfile.self_ext_off_multiples n hn
    exact Subsingleton.elim _ _

end
end TachikawaCharZero.TensorTwistWeights
