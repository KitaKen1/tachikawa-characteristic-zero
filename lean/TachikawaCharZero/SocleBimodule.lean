import TachikawaCharZero.ScalingSocle
import TachikawaCharZero.SplitInflation
import OAI.RingTheory.Tachikawa.HomBimodule

/-! The actual Hom_Q(X,X) bimodule for the previously constructed X.
Its normalized scalar coordinate constructs a genuine E-bimodule map
to every scaling twist. Restriction and dual projection recover eta.
Nonzero as an ordinary map is distinct from nonzero in the stable
category: the stable lift and evaluated nonzero class remain open. -/
namespace TachikawaCharZero.SocleBimodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa ScalingSocle
open scoped TensorProduct ModuleCat.Algebra

abbrev X := TensorProfile.X₂
abbrev B := ScalingSocle.B
abbrev S := HomBimodule.obj (k := ℚ) X X
abbrev Base := HomBimodule.Base (k := ℚ) X X
def xOne : X := TensorProfile.groundEquiv.symm 1

theorem ground_xOne : TensorProfile.groundEquiv xOne=1 :=
  TensorProfile.groundEquiv.apply_symm_apply 1

theorem character_eq_tensor : characterE=SplitInflation.tensorCharacter := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  change Starting.T_character a*Starting.T_character b=
    SplitInflation.tensorCharacter (a ⊗ₜ[ℚ] b)
  rw [SplitInflation.tensorCharacter_tmul]
  rfl

theorem ground_action (a : E) (x : X) :
    TensorProfile.groundEquiv (a • x)=characterE a*TensorProfile.groundEquiv x := by
  rw [character_eq_tensor]
  exact SplitInflation.groundEquiv_action a x

theorem xOne_action (a : E) : a • xOne=characterE a • xOne := by
  apply TensorProfile.groundEquiv.injective
  rw [ground_action,map_smul]
  rfl

def coordinate : Base →ₗ[ℚ] ℚ where
  toFun f := TensorProfile.groundEquiv (f xOne)
  map_add' f g := TensorProfile.groundEquiv.map_add (f xOne) (g xOne)
  map_smul' c f := TensorProfile.groundEquiv.map_smul c (f xOne)

theorem coordinate_left (a : E) (f : Base) :
    coordinate (a • f)=characterE a*coordinate f :=
  ground_action a (f xOne)

theorem coordinate_right (a : Eᵐᵒᵖ) (f : Base) :
    coordinate (a • f)=characterE a.unop*coordinate f := by
  change TensorProfile.groundEquiv (f (a.unop • xOne))=
    characterE a.unop*TensorProfile.groundEquiv (f xOne)
  rw [xOne_action,(show X →ₗ[ℚ] X from f).map_smul,TensorProfile.groundEquiv.map_smul]
  rfl

theorem coordinate_identity : coordinate (show Base from (LinearMap.id : X →ₗ[ℚ] X))=1 :=
  TensorProfile.groundEquiv.apply_symm_apply 1

def socleLinear (H : ℚ) (hH : H ≠ 0) : Base →ₗ[E]
    AlgebraInduction.Bimod (scaling H hH).toAlgHom where
  toFun f := coordinate f • zeta
  map_add' f g := by rw [map_add,add_smul]
  map_smul' a f := by
    change coordinate (a • f) • zeta=a*(coordinate f • zeta)
    rw [coordinate_left,mul_smul_comm,zeta_left,smul_smul,mul_comm]

theorem socleLinear_right (H : ℚ) (hH : H ≠ 0) (a : Eᵐᵒᵖ) (f : Base) :
    socleLinear H hH (a • f)=a • socleLinear H hH f := by
  change coordinate (a • f) • zeta=(coordinate f • zeta)*scaling H hH a.unop
  rw [coordinate_right,smul_mul_assoc,zeta_right,character_scaling,smul_smul,mul_comm]

def socleMap (H : ℚ) (hH : H ≠ 0) : S ⟶ UH H hH :=
  Enveloping.ofBimoduleHom (socleLinear H hH) (socleLinear_right H hH)

theorem socleMap_identity (H : ℚ) (hH : H ≠ 0) :
    Enveloping.twistedUnderlying (scaling H hH)
      (socleMap H hH (show S from (LinearMap.id : X →ₗ[ℚ] X)))=zeta := by
  change coordinate (show Base from (LinearMap.id : X →ₗ[ℚ] X)) • zeta=zeta
  rw [coordinate_identity,one_smul]

theorem socleMap_ne_zero (H : ℚ) (hH : H ≠ 0) : socleMap H hH ≠ 0 := by
  intro h
  have hz := socleMap_identity H hH
  rw [h] at hz
  exact zeta_ne_zero hz.symm

def representationSocle (H : ℚ) (hH : H ≠ 0) :
    Enveloping.regular (k := ℚ) (R := E) ⟶ UH H hH :=
  HomBimodule.representation X ≫ socleMap H hH

theorem representation_socle (H : ℚ) (hH : H ≠ 0) (a : E) :
    Enveloping.twistedUnderlying (scaling H hH)
      (representationSocle H hH (Enveloping.regularUnderlyingEquiv.symm a))=
        characterE a • zeta := by
  change TensorProfile.groundEquiv (a • xOne) • zeta=characterE a • zeta
  rw [ground_action,ground_xOne,mul_one]

def restrictedSUnderlying : restriction.obj S ≃ₗ[ℚ] Base where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro x
    change (show X →ₗ[ℚ] X from
      ((inclusionBE (@algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c)) •
        (show S from f))) x=c • (show Base from f) x
    rw [AlgHom.commutes]
    exact HomBimodule.k_smul_apply X X c (show S from f) x

def restrictedCharacterLinear : TwistedBimoduleObstruction.U →ₗ[ℚ] restriction.obj S :=
  restrictedSUnderlying.symm.toLinearMap.comp
    ((TwistedFactorization.character.toLinearMap.smulRight
        (show Base from (LinearMap.id : X →ₗ[ℚ] X))).comp
      (Enveloping.twistedUnderlying TwistedFactorization.theta).toLinearMap)

theorem restrictedCharacterLinear_tensor (r : B) (s : Bᵐᵒᵖ)
    (x : TwistedBimoduleObstruction.U) :
    restrictedCharacterLinear ((r ⊗ₜ[ℚ] s) • x)=
      (r ⊗ₜ[ℚ] s) • restrictedCharacterLinear x := by
  apply restrictedSUnderlying.injective
  apply LinearMap.ext
  intro z
  change TwistedFactorization.character
      (r*((show B from x)*TwistedFactorization.theta s.unop)) • z=
    inclusionB r • (TwistedFactorization.character (show B from x) •
      (inclusionB s.unop • z))
  apply TensorProfile.groundEquiv.injective
  rw [map_smul,ground_action,map_smul,ground_action,
    character_inclusion,character_inclusion,map_mul,map_mul,TwistedFactorization.character_theta]
  change (TwistedFactorization.character r*
      (TwistedFactorization.character (show B from x)*TwistedFactorization.character s.unop))*
      TensorProfile.groundEquiv z=_
  ring

def restrictedCharacterMap : TwistedBimoduleObstruction.U ⟶ restriction.obj S :=
  Enveloping.homOfLinear restrictedCharacterLinear restrictedCharacterLinear_tensor

theorem restricted_character_socle (H : ℚ) (hH : H ≠ 0) :
    restrictedCharacterMap ≫ restriction.map (socleMap H hH)=restrictedSocleMap H hH := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (restrictedUnderlying H hH).injective
  change coordinate (TwistedFactorization.character (show B from x) •
      (show Base from (LinearMap.id : X →ₗ[ℚ] X))) • zeta=
    TwistedFactorization.character (show B from x) • zeta
  generalize (show B from x)=b
  rw [map_smul,coordinate_identity,smul_eq_mul,mul_one]

theorem restricted_character_socle_eta (H : ℚ) (hH : H ≠ 0) :
    restrictedCharacterMap ≫ restriction.map (socleMap H hH) ≫ rhoMap H hH=
      TwistedBimoduleObstruction.etaMap := by
  rw [← Category.assoc,restricted_character_socle,restricted_socle_eta]

end
end TachikawaCharZero.SocleBimodule
