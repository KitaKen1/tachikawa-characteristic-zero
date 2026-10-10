import TachikawaCharZero.StartingSymmetric
import TachikawaCharZero.TwistedDerivedObstruction
import OAI.RingTheory.Tachikawa.ScaleDual
import OAI.RingTheory.Tachikawa.BimoduleLinear

/-! Actual rational scaling twists, their socle and the restriction square.
The projection onto DC tensor DC is an actual B-bimodule map after restriction.
The rank-one socle map from B_theta composes with it to the proved eta.
Stable lifts, perfect preservation under restriction and evaluation at X
remain separate obligations. The coordinate proofs adapt characteristic-
independent calculations from OpenAI Math's Socle.lean and Induction.lean
at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.ScalingSocle
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

abbrev A := Resolution.A
abbrev T := Starting.T
abbrev B := Starting.B
abbrev E := Starting.E
abbrev BE := TwistedBimoduleObstruction.BE
abbrev EE := Enveloping.Alg ℚ E E
abbrev inclusionC : A →ₐ[ℚ] T := TrivSqZeroExt.inlAlgHom ℚ A (DualBimodule ℚ A)
def inclusionB : B →ₐ[ℚ] E := Algebra.TensorProduct.map inclusionC inclusionC
def inclusionBE : BE →ₐ[ℚ] EE := Algebra.TensorProduct.map inclusionB inclusionB.op
abbrev restriction := AlgebraInduction.res (k := ℚ) (R := BE) (S := EE) inclusionBE
def characterE : E →ₐ[ℚ] ℚ :=
  Algebra.TensorProduct.productMap Starting.T_character Starting.T_character
def scaling (H : ℚ) (hH : H ≠ 0) : E ≃ₐ[ℚ] E :=
  Algebra.TensorProduct.congr (TrivialExtension.scaleDual H hH)
    (TrivialExtension.scaleDual H hH)
def zT : T := TrivSqZeroExt.inr
  (Resolution.character.toLinearMap : DualBimodule ℚ A)
def zeta : E := zT ⊗ₜ[ℚ] zT

theorem character_inclusion (a : B) :
    characterE (inclusionB a)=TwistedFactorization.character a := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b => rfl

theorem character_scaling (H : ℚ) (hH : H ≠ 0) (a : E) :
    characterE (scaling H hH a)=characterE a := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b => rfl

theorem scaling_inclusion (H : ℚ) (hH : H ≠ 0) (a : B) :
    scaling H hH (inclusionB a)=inclusionB a := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b =>
    change TrivialExtension.scaleDual H hH (TrivSqZeroExt.inl a) ⊗ₜ[ℚ]
      TrivialExtension.scaleDual H hH (TrivSqZeroExt.inl b)=
        TrivSqZeroExt.inl a ⊗ₜ[ℚ] TrivSqZeroExt.inl b
    rw [TrivialExtension.scaleDual_inl,TrivialExtension.scaleDual_inl]

theorem zT_left (a : T) : a*zT=Starting.T_character a • zT := by
  apply TrivSqZeroExt.ext
  · change a.fst*0=Starting.T_character a • (0:A)
    simp
  · apply LinearMap.ext
    intro c
    change Resolution.character (c*a.fst)+a.snd ((0:A)*c)=
      Starting.T_character a*Resolution.character c
    simp only [map_mul,zero_mul,map_zero,add_zero]
    exact mul_comm _ _

theorem zT_right (a : T) : zT*a=Starting.T_character a • zT := by
  apply TrivSqZeroExt.ext
  · change (0:A)*a.fst=Starting.T_character a • (0:A)
    simp
  · apply LinearMap.ext
    intro c
    change a.snd (c*(0:A))+Resolution.character (a.fst*c)=
      Starting.T_character a*Resolution.character c
    simp only [mul_zero,map_zero,zero_add,map_mul]
    rfl

theorem zeta_left (a : E) : a*zeta=characterE a • zeta := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_mul,map_add,add_smul,ha,hb]
  | tmul a b =>
    rw [zeta,Algebra.TensorProduct.tmul_mul_tmul]
    change (a*zT) ⊗ₜ[ℚ] (b*zT)=
      (Starting.T_character a*Starting.T_character b) • (zT ⊗ₜ[ℚ] zT)
    rw [zT_left,zT_left,TensorProduct.smul_tmul_smul]

theorem zeta_right (a : E) : zeta*a=characterE a • zeta := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [mul_add,map_add,add_smul,ha,hb]
  | tmul a b =>
    rw [zeta,Algebra.TensorProduct.tmul_mul_tmul]
    change (zT*a) ⊗ₜ[ℚ] (zT*b)=
      (Starting.T_character a*Starting.T_character b) • (zT ⊗ₜ[ℚ] zT)
    rw [zT_right,zT_right,TensorProduct.smul_tmul_smul]

theorem form_zeta : Starting.E_form.linear zeta=1 := by
  change Resolution.character 1*Resolution.character 1=1
  simp

theorem zeta_ne_zero : zeta ≠ 0 := by
  intro h
  have hz := form_zeta
  rw [h,map_zero] at hz
  exact zero_ne_one hz

theorem scaling_zeta (H : ℚ) (hH : H ≠ 0) :
    scaling H hH zeta=H^2 • zeta := by
  have hz : TrivialExtension.scaleDual H hH zT=H • zT := by
    apply TrivSqZeroExt.ext
    · change (0:A)=H • (0:A)
      simp
    · rfl
  change TrivialExtension.scaleDual H hH zT ⊗ₜ[ℚ]
    TrivialExtension.scaleDual H hH zT=H^2 • (zT ⊗ₜ[ℚ] zT)
  rw [hz]
  rw [TensorProduct.smul_tmul_smul,pow_two]

theorem form_scaling (H : ℚ) (hH : H ≠ 0) (a : E) :
    Starting.E_form.linear (scaling H hH a)=H^2*Starting.E_form.linear a := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb,mul_add]
  | tmul a b =>
    change (H*a.snd 1)*(H*b.snd 1)=H^2*(a.snd 1*b.snd 1)
    ring

def rho : E →ₗ[ℚ] DualBimodule ℚ B :=
  (TensorProduct.dualDistrib ℚ A A).comp
    (TensorProduct.map ((TrivSqZeroExt.sndHom A (DualBimodule ℚ A)).restrictScalars ℚ)
      ((TrivSqZeroExt.sndHom A (DualBimodule ℚ A)).restrictScalars ℚ))

theorem rho_tmul (a b : T) (x y : A) :
    rho (a ⊗ₜ[ℚ] b) (x ⊗ₜ[ℚ] y)=a.snd x*b.snd y := rfl

theorem rho_left (a : B) (z : E) : rho (inclusionB a*z)=a • rho z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,add_mul,ha,hb,add_smul]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [mul_add,map_add,hx,hy,smul_add]
    | tmul x y =>
      apply TensorProduct.ext'
      intro c d
      change rho ((inclusionC a ⊗ₜ[ℚ] inclusionC b)*(x ⊗ₜ[ℚ] y))
        (c ⊗ₜ[ℚ] d)=rho (x ⊗ₜ[ℚ] y) ((c ⊗ₜ[ℚ] d)*(a ⊗ₜ[ℚ] b))
      rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        rho_tmul,rho_tmul]
      change (a • x.snd+MulOpposite.op x.fst • (0:DualBimodule ℚ A)) c *
        (b • y.snd+MulOpposite.op y.fst • (0:DualBimodule ℚ A)) d=_
      simp only [smul_zero,add_zero]
      rfl

theorem rho_right (a : B) (z : E) :
    rho (z*inclusionB a)=MulOpposite.op a • rho z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,mul_add,ha,hb,MulOpposite.op_add,add_smul]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_mul,map_add,hx,hy,smul_add]
    | tmul x y =>
      apply TensorProduct.ext'
      intro c d
      change rho ((x ⊗ₜ[ℚ] y)*(inclusionC a ⊗ₜ[ℚ] inclusionC b))
        (c ⊗ₜ[ℚ] d)=rho (x ⊗ₜ[ℚ] y) ((a ⊗ₜ[ℚ] b)*(c ⊗ₜ[ℚ] d))
      rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        rho_tmul,rho_tmul]
      change (x.fst • (0:DualBimodule ℚ A)+MulOpposite.op a • x.snd) c *
        (y.fst • (0:DualBimodule ℚ A)+MulOpposite.op b • y.snd) d=_
      simp only [smul_zero,zero_add]
      rfl

theorem rho_zeta : rho zeta=TwistedFactorization.character.toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  rfl

abbrev UH (H : ℚ) (hH : H ≠ 0) := Enveloping.twistedRegular (scaling H hH)
def restrictedUnderlying (H : ℚ) (hH : H ≠ 0) : (restriction.obj (UH H hH)) ≃ₗ[ℚ] E where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (inclusionBE (@algebraMap ℚ BE _ (inferInstance : Semiring BE) inferInstance c)) •
      (show UH H hH from x)=c • (show E from x)
    rw [AlgHom.commutes]
    exact (Enveloping.twistedUnderlying (scaling H hH)).map_smul c (show UH H hH from x)

def rhoLinear (H : ℚ) (hH : H ≠ 0) :
    restriction.obj (UH H hH) →ₗ[ℚ] TwistedBimoduleObstruction.D :=
  TwistedBimoduleObstruction.bimoduleUnderlying.symm.toLinearMap.comp
    (rho.comp (restrictedUnderlying H hH).toLinearMap)

theorem rhoLinear_tensor (H : ℚ) (hH : H ≠ 0) (r : B) (s : Bᵐᵒᵖ)
    (x : restriction.obj (UH H hH)) :
    rhoLinear H hH ((r ⊗ₜ[ℚ] s) • x)=(r ⊗ₜ[ℚ] s) • rhoLinear H hH x := by
  apply TwistedBimoduleObstruction.bimoduleUnderlying.injective
  change rho (inclusionB r*((show E from x)*scaling H hH (inclusionB s.unop)))=
    r • MulOpposite.op s.unop • rho (show E from x)
  rw [scaling_inclusion,rho_left,rho_right]

def rhoMap (H : ℚ) (hH : H ≠ 0) :
    restriction.obj (UH H hH) ⟶ TwistedBimoduleObstruction.D :=
  Enveloping.homOfLinear (rhoLinear H hH) (rhoLinear_tensor H hH)

def restrictedSocleLinear (H : ℚ) (hH : H ≠ 0) :
    TwistedBimoduleObstruction.U →ₗ[ℚ] restriction.obj (UH H hH) :=
  (restrictedUnderlying H hH).symm.toLinearMap.comp
    ((TwistedFactorization.character.toLinearMap.smulRight zeta).comp
      (Enveloping.twistedUnderlying TwistedFactorization.theta).toLinearMap)

theorem socle_equivariance (H : ℚ) (hH : H ≠ 0) (r s b : B) :
    TwistedFactorization.character (r*(b*TwistedFactorization.theta s)) • zeta=
      inclusionB r*((TwistedFactorization.character b • zeta)*
        scaling H hH (inclusionB s)) := by
  rw [map_mul,map_mul,TwistedFactorization.character_theta,scaling_inclusion,
    smul_mul_assoc,zeta_right,mul_smul_comm,mul_smul_comm,zeta_left,
    character_inclusion,character_inclusion,smul_smul,smul_smul]
  congr 1
  ring

theorem restrictedSocleLinear_tensor (H : ℚ) (hH : H ≠ 0) (r : B) (s : Bᵐᵒᵖ)
    (x : TwistedBimoduleObstruction.U) :
    restrictedSocleLinear H hH ((r ⊗ₜ[ℚ] s) • x)=
      (r ⊗ₜ[ℚ] s) • restrictedSocleLinear H hH x := by
  apply (restrictedUnderlying H hH).injective
  change TwistedFactorization.character (r*((show B from x)*TwistedFactorization.theta s.unop)) • zeta=
    inclusionB r*((TwistedFactorization.character (show B from x) • zeta)*
      scaling H hH (inclusionB s.unop))
  exact socle_equivariance H hH r s.unop (show B from x)

def restrictedSocleMap (H : ℚ) (hH : H ≠ 0) :
    TwistedBimoduleObstruction.U ⟶ restriction.obj (UH H hH) :=
  Enveloping.homOfLinear (restrictedSocleLinear H hH) (restrictedSocleLinear_tensor H hH)

theorem restricted_socle_eta (H : ℚ) (hH : H ≠ 0) :
    restrictedSocleMap H hH ≫ rhoMap H hH=TwistedBimoduleObstruction.etaMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply TwistedBimoduleObstruction.bimoduleUnderlying.injective
  change rho (TwistedFactorization.character (show B from x) • zeta)=
    TwistedFactorization.eta (show B from x)
  rw [map_smul,rho_zeta]
  rfl

end
end TachikawaCharZero.ScalingSocle
