import OAI.RingTheory.Tachikawa.CompleteResolution

/-! Signed all-integer Hom cochains between actual chain complexes.
The differential retains the parity of the cochain degree; it is valid
over any field, including the rational field used by the final cone. -/
namespace TachikawaCharZero.SignedDownHom
noncomputable section
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def sign (a : ℤ) : k := (-1:k)^a

theorem sign_succ (a : ℤ) : sign (k:=k) (a+1) = - sign (k:=k) a := by
  simp only [sign,zpow_add_one₀ (neg_ne_zero.mpr (one_ne_zero : (1:k)≠0)),
    mul_neg,mul_one]

abbrev Cochain (P Q : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ) :=
  ∀ (i j : ℤ), i=j+a → (P.X i ⟶ Q.X j)

variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

/-- Package the equality proof in a Type to transport the module structure.
This characteristic-independent packaging adapts pinned OpenAI Math
DownHom.lean 238--252 (Apache-2.0); its characteristic-two differential
is not reused. -/
structure Index (a : ℤ) where
  i : ℤ
  j : ℤ
  h : i=j+a

def indexEquiv (a : ℤ) : Cochain P Q a ≃ (∀ t : Index a, P.X t.i ⟶ Q.X t.j) where
  toFun f t := f t.i t.j t.h
  invFun f i j h := f ⟨i,j,h⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (a : ℤ) : AddCommGroup (Cochain P Q a) := (indexEquiv a).addCommGroup
instance (a : ℤ) : Module k (Cochain P Q a) :=
  AddEquiv.module k { toEquiv := indexEquiv a, map_add' := fun _ _ => rfl }

@[simp] theorem zero_apply {a : ℤ} (i j : ℤ) (h : i=j+a) :
    (0 : Cochain P Q a) i j h=0 := rfl

@[simp] theorem add_apply {a : ℤ} (f g : Cochain P Q a) (i j : ℤ) (h : i=j+a) :
    (f+g) i j h=f i j h+g i j h := rfl

@[simp] theorem smul_apply {a : ℤ} (c : k) (f : Cochain P Q a)
    (i j : ℤ) (h : i=j+a) : (c • f) i j h=c • f i j h := rfl

def diff {a : ℤ} (f : Cochain P Q a) : Cochain P Q (a+1) :=
  fun i j he => f i (j+1) (by omega) ≫ Q.d (j+1) j -
    sign (k:=k) a • (P.d i (i-1) ≫ f (i-1) j (by omega))

theorem diff_add {a : ℤ} (f g : Cochain P Q a) :
    diff (k:=k) (f+g)=diff (k:=k) f+diff (k:=k) g := by
  funext i j he
  simp only [diff,add_apply,add_comp,comp_add,smul_add]
  abel

theorem diff_smul {a : ℤ} (c : k) (f : Cochain P Q a) :
    diff (k:=k) (c • f)=c • diff (k:=k) f := by
  funext i j he
  simp only [diff,smul_apply,Linear.smul_comp,Linear.comp_smul,smul_sub,
    smul_smul,mul_comm]

theorem diff_diff {a : ℤ} (f : Cochain P Q a) :
    diff (k:=k) (diff (k:=k) f)=0 := by
  funext i j he
  simp only [diff,sub_comp,comp_sub,Linear.smul_comp,Linear.comp_smul,
    Category.assoc,Q.d_comp_d,comp_zero,zero_apply]
  rw [← Category.assoc (P.d i (i-1)) (P.d (i-1) (i-1-1)),P.d_comp_d,zero_comp,
    smul_zero,sub_zero,sign_succ,neg_smul]
  abel

def differential (a : ℤ) : Cochain P Q a →ₗ[k] Cochain P Q (a+1) where
  toFun := diff (k:=k)
  map_add' := diff_add (k:=k)
  map_smul' c f := by simpa only [RingHom.id_apply] using diff_smul (k:=k) c f

def Closed {a : ℤ} (f : Cochain P Q a) : Prop := diff (k:=k) f=0

theorem closed_diff {a : ℤ} (f : Cochain P Q a) : Closed (k:=k) (diff (k:=k) f) :=
  diff_diff (k:=k) f

end
end TachikawaCharZero.SignedDownHom
