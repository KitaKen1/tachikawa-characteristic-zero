import TachikawaCharZero.SignedConeCochains
import TachikawaCharZero.SignedCochainCalculus

/-! Signed differential comparison for actual assembled cone cochains.
The projection method follows pinned OpenAI Math Cone.lean 301--361
(fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0), with the
negative shifted differential and degree-parity factors retained. -/
namespace TachikawaCharZero.SignedConeDifferential
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open OAI.Tachikawa.CompleteCone SignedDownHom SignedConeCochains
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

@[reassoc] theorem d_left (i : ℤ) : (C v).d i (i-1) ≫ left v (i-1) =
    -(left v i) ≫ B.d (i-1) (i-1-1) :=
  homotopyCofiber.d_fstX v i (i-1) (i-1-1)
    (by change i-1+1=i; omega) (by change i-1-1+1=i-1; omega)

@[reassoc] theorem d_right (i : ℤ) : (C v).d i (i-1) ≫ right v (i-1) =
    left v i ≫ v.f (i-1)+right v i ≫ A.d i (i-1) :=
  homotopyCofiber.d_sndX v i (i-1) (by change i-1+1=i; omega)

theorem apply_inl_d {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain D B a) (i s t j : ℤ)
    (hs : (ComplexShape.down ℤ).Rel t s) (hj : (ComplexShape.down ℤ).Rel t j)
    (he : i=s+a) (he' : i=j+a) :
    f i s he ≫ homotopyCofiber.inlX v s t hs ≫ (C v).d t j =
      -(f i j he' ≫ B.d j (j-1) ≫ inLeft v j)+
        f i j he' ≫ v.f j ≫ inRight v j := by
  have H : s=j := by change s+1=t at hs; change j+1=t at hj; omega
  cases H
  change f i s he ≫ homotopyCofiber.inlX v s t hs ≫ homotopyCofiber.d v t s = _
  rw [homotopyCofiber.inlX_d v t s (s-1) hs (by change s-1+1=s; omega)]
  simp only [comp_add,comp_neg]

theorem diff_assemble {a : ℤ} (f : Cochain A A (a-1)) (g : Cochain B B (a-1))
    (c : Cochain B A (a-1-1)) :
    diffAt (k:=k) (assemble v f g c) =
      assemble v (diffAt (k:=k) f) (-diffAt (k:=k) g)
        (diffAt (k:=k) c+post g v-sign (k:=k) (a-1) • pre v f) := by
  have hs : sign (k:=k) (a-1-1)= -sign (k:=k) (a-1) := by
    simpa only [sub_add_cancel,neg_neg] using
      congrArg Neg.neg (sign_succ (k:=k) (a-1-1)).symm
  funext i j h
  simp only [diffAt,assemble,SignedDownHom.add_apply,SignedDownHom.sub_apply,
    SignedDownHom.neg_apply,SignedDownHom.smul_apply,pre,post,
    comp_add,add_comp,comp_sub,sub_comp,Linear.comp_smul,Linear.smul_comp,
    comp_neg,neg_comp,Category.assoc,d_left_assoc,d_right_assoc,inRight_d]
  rw [apply_inl_d v g (i-1) (j+1-1) (j+1) j
    (by change j+1-1+1=j+1; omega) (by rfl) _ (by omega)]
  simp only [comp_add,comp_neg,smul_add,smul_neg,neg_smul,hs]
  rw [← Category.assoc (g (i-1) (j-1+1) _) (B.d (j-1+1) (j-1)) (inLeft v j),
    d_post_eq g (i-1) (j-1+1) j (j-1) (by omega) _ (by omega),Category.assoc]
  abel

variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB in
theorem low_diffAt {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    low v (diffAt (k:=k) f)=diffAt (k:=k) (low v f) := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble,low_assemble]

include hAB in
theorem high_diffAt {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    high v (diffAt (k:=k) f)= -diffAt (k:=k) (high v f) := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble,high_assemble]

include hAB in
theorem cross_diffAt {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    cross v (diffAt (k:=k) f)=diffAt (k:=k) (cross v f)+
      post (high v f) v-sign (k:=k) (a-1) • pre v (low v f) := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble,cross_assemble]

/-- Actual cross component of the cone differential on diagonal cochains. -/
def connecting {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) : Cochain B A a :=
  post g v-sign (k:=k) a • pre v f

/-- Input order agrees with the existing two-branch Delta convention. -/
def delta {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) : Cochain B A a :=
  pre v f-sign (k:=k) a • post g v

theorem connecting_delta {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) :
    connecting (k:=k) v f g= -sign (k:=k) a • delta (k:=k) v f g := by
  funext i j h
  simp only [connecting,delta,SignedDownHom.sub_apply,SignedDownHom.smul_apply]
  rw [neg_smul,smul_sub,smul_smul,SignedDownHom.sign_mul_self,one_smul]
  abel

end
end TachikawaCharZero.SignedConeDifferential
