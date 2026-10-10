import TachikawaCharZero.SignedDownHom

/-! Integer-degree transport and boundary calculus for the signed Hom
differential. The component transport lemmas adapt pinned OpenAI Math
DownHom.lean 150--158 (fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Apache-2.0); all differential and boundary formulas retain the signs. -/
namespace TachikawaCharZero.SignedDownHom
noncomputable section
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℤ}

theorem sign_mul_self (a : ℤ) : sign (k:=k) a * sign (k:=k) a=1 := by
  simp only [sign,← mul_zpow,neg_mul_neg,one_mul,one_zpow]

@[simp] theorem neg_apply {a : ℤ} (f : Cochain P Q a) (i j : ℤ) (h : i=j+a) :
    (-f) i j h= -(f i j h) := rfl

@[simp] theorem sub_apply {a : ℤ} (f g : Cochain P Q a) (i j : ℤ) (h : i=j+a) :
    (f-g) i j h=f i j h-g i j h := rfl

theorem d_pre_eq {a : ℤ} (f : Cochain P Q a) (p i i' j : ℤ)
    (he : i=i') (hi : i=j+a) (hi' : i'=j+a) :
    P.d p i ≫ f i j hi=P.d p i' ≫ f i' j hi' := by subst i'; rfl

theorem d_post_eq {a : ℤ} (f : Cochain P Q a) (i j j' q : ℤ)
    (he : j=j') (hi : i=j+a) (hi' : i=j'+a) :
    f i j hi ≫ Q.d j q=f i j' hi' ≫ Q.d j' q := by subst j'; rfl

/-- The same signed differential, indexed by its output degree. -/
def diffAt {a : ℤ} (f : Cochain P Q (a-1)) : Cochain P Q a :=
  fun i j he => f i (j+1) (by omega) ≫ Q.d (j+1) j -
    sign (k:=k) (a-1) • (P.d i (i-1) ≫ f (i-1) j (by omega))

theorem closed_iff_diffAt {a : ℤ} (f : Cochain P Q (a-1)) :
    Closed (k:=k) f ↔ diffAt (k:=k) f=0 := by
  constructor
  · intro hf
    funext i j he
    have hh := congrArg (fun g => g i j (show i=j+((a-1)+1) by omega)) hf
    simpa only [diffAt,diff,zero_apply] using hh
  · intro hf
    unfold Closed
    funext i j he
    have hh := congrArg (fun g => g i j (show i=j+a by omega)) hf
    simpa only [diffAt,diff,zero_apply] using hh

theorem closed_diffAt {a : ℤ} (f : Cochain P Q (a-1)) :
    Closed (k:=k) (diffAt (k:=k) f) := by
  unfold Closed
  funext i j he
  have hh := congrArg (fun g => g i j (show i=j+((a-1+1)+1) by omega))
    (diff_diff (k:=k) f)
  simpa only [diffAt,diff,zero_apply,sub_add_cancel] using hh

theorem diffAt_add {a : ℤ} (f g : Cochain P Q (a-1)) :
    diffAt (k:=k) (f+g)=diffAt (k:=k) f+diffAt (k:=k) g := by
  funext i j he
  simp only [diffAt,add_apply,add_comp,comp_add,smul_add]
  abel

theorem diffAt_smul {a : ℤ} (t : k) (f : Cochain P Q (a-1)) :
    diffAt (k:=k) (t • f)=t • diffAt (k:=k) f := by
  funext i j he
  simp only [diffAt,smul_apply,Linear.smul_comp,Linear.comp_smul,
    smul_sub,smul_smul,mul_comm]

theorem diffAt_neg {a : ℤ} (f : Cochain P Q (a-1)) :
    diffAt (k:=k) (-f)= -diffAt (k:=k) f := by
  funext i j he
  simp only [diffAt,neg_apply,neg_comp,comp_neg,smul_neg]
  abel

theorem diffAt_zero (a : ℤ) : diffAt (k:=k) (0 : Cochain P Q (a-1))=0 := by
  funext i j he
  simp only [diffAt,zero_apply,comp_zero,zero_comp,smul_zero,sub_zero]

theorem closed_add {a : ℤ} {f g : Cochain P Q a}
    (hf : Closed (k:=k) f) (hg : Closed (k:=k) g) : Closed (k:=k) (f+g) := by
  unfold Closed at *
  rw [diff_add,hf,hg,add_zero]

theorem closed_neg {a : ℤ} {f : Cochain P Q a} (hf : Closed (k:=k) f) :
    Closed (k:=k) (-f) := by
  unfold Closed at *
  have hn : diff (k:=k) (-f)= -diff (k:=k) f := by
    funext i j he
    simp only [diff,neg_apply,neg_comp,comp_neg,smul_neg]
    abel
  rw [hn,hf,neg_zero]

theorem closed_sub {a : ℤ} {f g : Cochain P Q a}
    (hf : Closed (k:=k) f) (hg : Closed (k:=k) g) : Closed (k:=k) (f-g) := by
  rw [sub_eq_add_neg]
  exact closed_add hf (closed_neg hg)

def Boundary {a : ℤ} (f : Cochain P Q a) : Prop :=
  ∃ g : Cochain P Q (a-1), diffAt (k:=k) g=f

theorem boundary_diffAt {a : ℤ} (f : Cochain P Q (a-1)) :
    Boundary (k:=k) (diffAt (k:=k) f) := ⟨f,rfl⟩

theorem boundary_closed {a : ℤ} {f : Cochain P Q a} (hf : Boundary (k:=k) f) :
    Closed (k:=k) f := by
  obtain ⟨g,rfl⟩ := hf
  exact closed_diffAt g

theorem boundary_add {a : ℤ} {f g : Cochain P Q a}
    (hf : Boundary (k:=k) f) (hg : Boundary (k:=k) g) : Boundary (k:=k) (f+g) := by
  obtain ⟨s,rfl⟩ := hf
  obtain ⟨t,rfl⟩ := hg
  exact ⟨s+t,diffAt_add s t⟩

theorem boundary_neg {a : ℤ} {f : Cochain P Q a} (hf : Boundary (k:=k) f) :
    Boundary (k:=k) (-f) := by
  obtain ⟨s,rfl⟩ := hf
  exact ⟨-s,diffAt_neg s⟩

theorem boundary_sub {a : ℤ} {f g : Cochain P Q a}
    (hf : Boundary (k:=k) f) (hg : Boundary (k:=k) g) : Boundary (k:=k) (f-g) := by
  rw [sub_eq_add_neg]
  exact boundary_add hf (boundary_neg hg)

theorem boundary_smul {a : ℤ} (t : k) {f : Cochain P Q a}
    (hf : Boundary (k:=k) f) : Boundary (k:=k) (t • f) := by
  obtain ⟨s,rfl⟩ := hf
  exact ⟨t • s,diffAt_smul t s⟩

theorem boundary_zero (a : ℤ) : Boundary (k:=k) (0 : Cochain P Q a) :=
  ⟨0,diffAt_zero a⟩

def pre (u : S ⟶ P) {a : ℤ} (f : Cochain P Q a) : Cochain S Q a :=
  fun i j h => u.f i ≫ f i j h
def post {a : ℤ} (f : Cochain P Q a) (u : Q ⟶ S) : Cochain P S a :=
  fun i j h => f i j h ≫ u.f j

end
end TachikawaCharZero.SignedDownHom
