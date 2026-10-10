import TachikawaCharZero.SignedRephasing

/-! Signed closed cochains and actual translated chain maps, in both
directions. The inverse and nullhomotopy constructions adapt pinned
OpenAI Math DownHom.lean 161--210 (Apache-2.0, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb), retaining all component phases.
No characteristic assumption or evaluation-surjectivity premise is added. -/
namespace TachikawaCharZero.SignedChainComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open OAI.Tachikawa SignedDownHom SignedRephasing
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

theorem phase_succ (a j : ℤ) :
    phase (k:=k) a (j+1)=phase (k:=k) a j * sign (k:=k) a := by
  simp only [phase,zpow_add_one₀ (SignedRephasing.sign_ne_zero (k:=k) a)]

def ofChain {a : ℤ} (u : translate P a ⟶ Q) : Cochain P Q a :=
  fun _i j h => phase (k:=k) a j • ((P.XIsoOfEq h).hom ≫ u.f j)

theorem ofChain_apply {a : ℤ} (u : translate P a ⟶ Q) (j : ℤ) :
    ofChain (k:=k) u (j+a) j rfl=phase (k:=k) a j • u.f j := by
  simp only [ofChain,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp]

theorem ofChain_comm {a : ℤ} (u : translate P a ⟶ Q)
    (i j l m : ℤ) (hi : i=j+a) (hl : l=m+a) (hj : j=m+1) :
    ofChain (k:=k) u i j hi ≫ Q.d j m =
      sign (k:=k) a • (P.d i l ≫ ofChain (k:=k) u l m hl) := by
  subst i
  subst l
  subst j
  simp only [ofChain_apply,Linear.smul_comp,Linear.comp_smul,smul_smul]
  have hu := u.comm (m+1) m
  change u.f (m+1) ≫ Q.d (m+1) m=P.d (m+1+a) (m+a) ≫ u.f m at hu
  rw [hu,phase_succ,mul_comm]

theorem ofChain_closed {a : ℤ} (u : translate P a ⟶ Q) :
    Closed (k:=k) (ofChain (k:=k) u) := by
  unfold SignedDownHom.Closed
  funext i j he
  exact sub_eq_zero.mpr (ofChain_comm u i (j+1) (i-1) j (by omega) (by omega) rfl)

theorem to_ofChain {a : ℤ} (u : translate P a ⟶ Q) :
    toChain (ofChain (k:=k) u) (ofChain_closed u)=u := by
  ext j
  simp only [toChain,rephase,ofChain_apply,smul_smul,phase_mul_self,one_smul]

theorem of_toChain {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f) :
    ofChain (k:=k) (toChain f hf)=f := by
  funext i j h
  subst i
  simp only [ofChain_apply,toChain,rephase,smul_smul,phase_mul_self,one_smul]

def closedChainEquiv (a : ℤ) :
    {f : Cochain P Q a // Closed (k:=k) f} ≃ (translate P a ⟶ Q) where
  toFun f := toChain f.val f.property
  invFun u := ⟨ofChain (k:=k) u,ofChain_closed u⟩
  left_inv f := Subtype.ext (of_toChain f.val f.property)
  right_inv u := to_ofChain u

theorem boundary_phase (a j : ℤ) :
    -sign (k:=k) (a-1) * phase (k:=k) a (j-1)=phase (k:=k) a j := by
  have hn : -sign (k:=k) (a-1)=sign (k:=k) a := by
    rw [← sign_succ,sub_add_cancel]
  rw [hn,phase_pred,mul_left_comm,SignedDownHom.sign_mul_self,mul_one]

theorem ofHomotopy_boundary {a : ℤ} {u : translate P a ⟶ Q}
    (h : Homotopy u 0) : Boundary (k:=k) (ofChain (k:=k) u) := by
  let c : Cochain P Q (a-1) := fun i j he =>
    phase (k:=k) a (j-1) •
      ((P.XIsoOfEq (show i=(j-1)+a by omega)).hom ≫ h.hom (j-1) j)
  refine ⟨c,?_⟩
  funext i j he
  subst i
  rw [ofChain_apply]
  have hh := h.comm j
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)] at hh
  simp only [zero_f,add_zero] at hh
  change u.f j=P.d (j+a) (j-1+a) ≫ h.hom (j-1) j+
    h.hom j (j+1) ≫ Q.d (j+1) j at hh
  have ht (p p' q : ℤ) (he : p=p') :
      (P.XIsoOfEq (congrArg (fun t => t+a) he)).hom ≫ h.hom p' q=h.hom p q := by
    subst p'
    simp
  dsimp only [diffAt,c]
  rw [Linear.smul_comp,Linear.comp_smul]
  rw [← Category.assoc (P.d (j+a) (j+a-1)),P.d_comp_XIsoOfEq_hom]
  rw [ht j (j+1-1) (j+1) (by omega),show j+1-1=j by omega]
  rw [sub_eq_add_neg,← neg_smul,smul_smul,boundary_phase,← smul_add]
  apply congrArg (fun z => phase (k:=k) a j • z)
  exact (add_comm _ _).trans hh.symm

theorem homotopy_boundary {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f)
    (h : Homotopy (toChain f hf) 0) : Boundary (k:=k) f := by
  simpa only [of_toChain] using ofHomotopy_boundary (k:=k) h

theorem boundary_iff_homotopy {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f) :
    Boundary (k:=k) f ↔ Nonempty (Homotopy (toChain f hf) 0) :=
  ⟨boundary_homotopy f hf,fun ⟨h⟩ => homotopy_boundary f hf h⟩

end
end TachikawaCharZero.SignedChainComparison
