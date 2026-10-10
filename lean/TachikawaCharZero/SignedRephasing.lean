import TachikawaCharZero.SignedCochainCalculus

/-! Turn an actual signed closed cochain into an unsigned translated chain
map by target-component rephasing. Target degree zero is unchanged.
The unsigned translate adapts pinned OpenAI Math DownHom.lean 87--117
(fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0); the signed
rephasing proof is new. The boundary-to-homotopy construction adapts
lines 217--234 with the component phases retained. The converse and
complete-Hom evaluation comparisons are still separate obligations. -/
namespace TachikawaCharZero.SignedRephasing
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open OAI.Tachikawa SignedDownHom
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

def phase (a j : ℤ) : k := sign (k:=k) a ^ j

theorem sign_ne_zero (a : ℤ) : sign (k:=k) a≠0 := by
  intro h
  have hs := SignedDownHom.sign_mul_self (k:=k) a
  rw [h,zero_mul] at hs
  exact zero_ne_one hs

theorem phase_ne_zero (a j : ℤ) : phase (k:=k) a j≠0 := by
  exact zpow_ne_zero j (sign_ne_zero a)

theorem phase_zero (a : ℤ) : phase (k:=k) a 0=1 := by simp only [phase,zpow_zero]

theorem phase_mul_self (a j : ℤ) : phase (k:=k) a j * phase (k:=k) a j=1 := by
  simp only [phase,← mul_zpow,SignedDownHom.sign_mul_self,one_zpow]

theorem phase_succ_mul (a j : ℤ) :
    phase (k:=k) a (j+1)*sign (k:=k) a=phase (k:=k) a j := by
  simp only [phase,zpow_add_one₀ (sign_ne_zero (k:=k) a),mul_assoc,
    SignedDownHom.sign_mul_self,mul_one]

theorem phase_pred (a j : ℤ) :
    phase (k:=k) a (j-1)=phase (k:=k) a j * sign (k:=k) a := by
  simpa only [sub_add_cancel] using (phase_succ_mul (k:=k) a (j-1)).symm

def rephase {a : ℤ} (f : Cochain P Q a) : Cochain P Q a :=
  fun i j h => phase (k:=k) a j • f i j h

theorem rephase_involutive {a : ℤ} (f : Cochain P Q a) :
    rephase (k:=k) (rephase (k:=k) f)=f := by
  funext i j h
  simp only [rephase,smul_smul,phase_mul_self,one_smul]

theorem rephase_target_zero {a : ℤ} (f : Cochain P Q a) (i : ℤ) (h : i=0+a) :
    rephase (k:=k) f i 0 h=f i 0 h := by
  simp only [rephase,phase_zero,one_smul]

theorem rephase_comm {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f)
    (i j l m : ℤ) (hi : i=j+a) (hl : l=m+a) (hj : j=m+1) :
    rephase (k:=k) f i j hi ≫ Q.d j m =
      P.d i l ≫ rephase (k:=k) f l m hl := by
  subst j
  have hh : l=i-1 := by omega
  subst l
  have hc := congrArg (fun g => g i m (show i=m+(a+1) by omega)) hf
  change f i (m+1) _ ≫ Q.d (m+1) m-
      sign (k:=k) a • (P.d i (i-1) ≫ f (i-1) m _) =0 at hc
  have he := sub_eq_zero.mp hc
  simp only [rephase,Linear.smul_comp,Linear.comp_smul]
  rw [he,smul_smul,phase_succ_mul]
  exact congrArg (fun t => phase (k:=k) a m • t)
    (d_pre_eq f i (i-1) (m+a) m hh.symm _ _)

abbrev translate (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ) :
    ChainComplex (ModuleCat.{0} R) ℤ where
  X i := P.X (i+a)
  d i j := P.d (i+a) (j+a)
  shape i j h := P.shape _ _ (by
    intro he
    apply h
    change j+1=i
    change j+a+1=i+a at he
    omega)
  d_comp_d' i j l _ _ := P.d_comp_d _ _ _

theorem translate_exact (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    (hP : ComplexExact P) : ComplexExact (translate P a) := by
  intro j
  change Function.Exact (P.d (j+1+a) (j+a)) (P.d (j+a) (j-1+a))
  rw [show j+1+a=j+a+1 by omega,show j-1+a=j+a-1 by omega]
  exact hP (j+a)

theorem translate_totallyAcyclic (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    (hP : TotallyAcyclic P) : TotallyAcyclic (translate P a) := by
  refine ⟨translate_exact P a hP.1,?_⟩
  intro j f hf
  change f.comp (P.d (j+1+a) (j+a)).hom=0 at hf
  change ∃ g : P.X (j-1+a) →ₗ[R] R, g.comp (P.d (j+a) (j-1+a)).hom=f
  rw [show j+1+a=j+a+1 by omega] at hf
  rw [show j-1+a=j+a-1 by omega]
  exact hP.2 (j+a) f hf

def toChain {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f) : translate P a ⟶ Q where
  f j := rephase (k:=k) f (j+a) j rfl
  comm' i j hij := rephase_comm f hf (i+a) i (j+a) j rfl rfl (by
    change j+1=i at hij
    omega)

theorem toChain_target_zero {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f) :
    (toChain f hf).f 0=f (0+a) 0 rfl := rephase_target_zero f _ _

/-- Actual signed boundaries give actual nullhomotopies after rephasing. -/
theorem boundary_homotopy {a : ℤ} (f : Cochain P Q a)
    (hf : Closed (k:=k) f) (hb : Boundary (k:=k) f) :
    Nonempty (Homotopy (toChain f hf) 0) := by
  obtain ⟨c,hc⟩ := hb
  classical
  let h : ∀ p q, (translate P a).X p ⟶ Q.X q :=
    fun p q => if he : q=p+1 then phase (k:=k) a p • c (p+a) q (by omega) else 0
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro p q hpq
    change ¬ p+1=q at hpq
    simp only [h,dite_eq_right (Ne.symm hpq)]
  · intro j
    rw [dNext_eq _
        (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
      prevD_eq _
        (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)]
    simp only [toChain,zero_f,add_zero,h,
      dite_eq_left (show j=j-1+1 by omega),dite_eq_left rfl,
      Linear.comp_smul,Linear.smul_comp]
    change phase (k:=k) a j • f (j+a) j rfl =
      phase (k:=k) a (j-1) • (P.d (j+a) (j-1+a) ≫ c (j-1+a) j (by omega)) +
        phase (k:=k) a j • (c (j+a) (j+1) (by omega) ≫ Q.d (j+1) j)
    have hr := congrArg (fun g => g (j+a) j rfl) hc
    dsimp only [diffAt] at hr
    rw [d_pre_eq c (j+a) (j+a-1) (j-1+a) j (by omega) (by omega) (by omega)] at hr
    have hn : -sign (k:=k) (a-1)=sign (k:=k) a := by
      rw [← sign_succ,sub_add_cancel]
    rw [← hr,phase_pred,smul_sub,sub_eq_add_neg,← smul_neg,← neg_smul,hn,smul_smul]
    abel

end
end TachikawaCharZero.SignedRephasing
