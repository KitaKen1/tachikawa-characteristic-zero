import TachikawaCharZero.SignedDownHom
import OAI.RingTheory.Tachikawa.GenericCompleteCone

/-! Actual all-integer cone cochains split into low, high and cross blocks.
The characteristic-independent projection/assembly calculation is adapted
from OpenAI Math Cone.lean 195--296 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0), using SignedDownHom.Cochain and no CharP 2 wrapper.
The source's characteristic-two differential/boundary proof is not reused. -/
namespace TachikawaCharZero.SignedConeCochains
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open OAI.Tachikawa.CompleteCone SignedDownHom
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
abbrev C := complex v
abbrev iL (j : ℤ) := homotopyCofiber.inlX v j (j+1) (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)
abbrev pL (j : ℤ) := homotopyCofiber.fstX v (j+1) j (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)

def low {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain A A a :=
  fun i j h => inRight v i ≫ f i j h ≫ right v j
def high {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain B B a :=
  fun i j h => iL v i ≫ f (i+1) (j+1) (by omega) ≫ pL v j
def cross {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain B A (a-1) :=
  fun i j h => iL v i ≫ f (i+1) j (by omega) ≫ right v j

def assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a)
    (c : Cochain B A (a-1)) : Cochain (C v) (C v) a := fun i j h =>
  right v i ≫ f i j h ≫ inRight v j +
  left v i ≫ g (i-1) (j-1) (by omega) ≫ inLeft v j +
  left v i ≫ c (i-1) j (by omega) ≫ inRight v j

theorem inl_fst_apply {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain B D a) (p p' t j : ℤ)
    (hp : (ComplexShape.down ℤ).Rel t p) (hp' : (ComplexShape.down ℤ).Rel t p')
    (he : p=j+a) (he' : p'=j+a) :
    homotopyCofiber.inlX v p t hp ≫ homotopyCofiber.fstX v t p' hp' ≫ f p' j he' = f p j he := by
  have hh : p'=p := by change p+1=t at hp; change p'+1=t at hp'; omega
  cases hh
  simp only [homotopyCofiber.inlX_fstX_assoc]
theorem apply_inl_fst {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain D B a) (i p p' t : ℤ)
    (hp : (ComplexShape.down ℤ).Rel t p) (hp' : (ComplexShape.down ℤ).Rel t p')
    (he : i=p+a) (he' : i=p'+a) :
    f i p' he' ≫ homotopyCofiber.inlX v p' t hp' ≫ homotopyCofiber.fstX v t p hp = f i p he := by
  have hh : p'=p := by change p+1=t at hp; change p'+1=t at hp'; omega
  cases hh
  simp only [homotopyCofiber.inlX_fstX,Category.comp_id]
theorem block_transport {a : ℤ} (f : Cochain (C v) (C v) a)
    (p q i j i' j' : ℤ) (hi : (ComplexShape.down ℤ).Rel i p)
    (hi' : (ComplexShape.down ℤ).Rel i' p) (hj : (ComplexShape.down ℤ).Rel j q)
    (hj' : (ComplexShape.down ℤ).Rel j' q) (he : i=j+a) (he' : i'=j'+a) :
    homotopyCofiber.inlX v p i hi ≫ f i j he ≫ homotopyCofiber.fstX v j q hj =
    homotopyCofiber.inlX v p i' hi' ≫ f i' j' he' ≫ homotopyCofiber.fstX v j' q hj' := by
  have H : i'=i := by change p+1=i at hi; change p+1=i' at hi'; omega
  cases H
  have H : j'=j := by change q+1=j at hj; change q+1=j' at hj'; omega
  cases H; rfl
theorem cross_transport {a : ℤ} (f : Cochain (C v) (C v) a)
    (p i i' j : ℤ) (hi : (ComplexShape.down ℤ).Rel i p)
    (hi' : (ComplexShape.down ℤ).Rel i' p) (he : i=j+a) (he' : i'=j+a) :
    homotopyCofiber.inlX v p i hi ≫ f i j he ≫ right v j =
    homotopyCofiber.inlX v p i' hi' ≫ f i' j he' ≫ right v j := by
  have H : i'=i := by change p+1=i at hi; change p+1=i' at hi'; omega
  cases H; rfl

theorem low_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    low v (assemble v f g c) = f := by
  funext i j h
  simp only [assemble,low,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inrX_fstX_assoc,
      homotopyCofiber.inrX_sndX_assoc,homotopyCofiber.inlX_sndX,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,comp_zero,add_zero]
theorem high_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    high v (assemble v f g c) = g := by
  funext i j h
  simp only [assemble,high,iL,pL,left,right,inLeft,inRight,add_comp,
      Category.assoc,homotopyCofiber.inrX_fstX,comp_zero,add_zero,zero_add]
  rw [apply_inl_fst v g _ j _ _ _ _ (by omega) _,inl_fst_apply v g _ _ _ _ _ _ h _]
theorem cross_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    cross v (assemble v f g c) = c := by
  funext i j h
  simp only [assemble,cross,iL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_sndX_assoc,homotopyCofiber.inlX_sndX,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,comp_zero,add_zero,zero_add]

  exact inl_fst_apply v c _ _ _ _ _ _ h _
variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB in
theorem assemble_blocks {a : ℤ} (f : Cochain (C v) (C v) a) :
    assemble v (low v f) (high v f) (cross v f) = f := by
  funext i j h
  apply homotopyCofiber.ext_from_X v (i-1) i (by change i-1+1=i; omega)
  · apply homotopyCofiber.ext_to_X v j (j-1) (by change j-1+1=j; omega)
    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_fstX_assoc,homotopyCofiber.inlX_sndX_assoc,
      homotopyCofiber.inlX_fstX,homotopyCofiber.inrX_fstX,
      Category.comp_id,zero_comp,comp_zero,add_zero,zero_add]
      exact block_transport v f _ _ _ _ _ _ _ _ _ _ _ _

    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_fstX_assoc,homotopyCofiber.inlX_sndX_assoc,
      homotopyCofiber.inlX_sndX,homotopyCofiber.inrX_sndX,
      Category.comp_id,zero_comp,comp_zero,zero_add]
      exact cross_transport v f _ _ _ _ _ _ _ _

  · apply homotopyCofiber.ext_to_X v j (j-1) (by change j-1+1=j; omega)
    · simpa only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,sub_add_cancel,add_sub_cancel_right,homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc,homotopyCofiber.inrX_fstX_assoc,
      homotopyCofiber.inrX_sndX_assoc,homotopyCofiber.inlX_fstX,
      homotopyCofiber.inlX_sndX,homotopyCofiber.inrX_fstX,
      homotopyCofiber.inrX_sndX,Category.id_comp,Category.comp_id,zero_comp,comp_zero,add_zero,zero_add] using (hAB i (j-1) (inRight v i ≫ f i j h ≫ left v j)).symm
    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,
      Category.assoc,homotopyCofiber.inrX_fstX_assoc,homotopyCofiber.inrX_sndX_assoc,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,add_zero]
include hAB in
theorem low_post_d (i j l : ℤ) (f : (C v).X i ⟶ (C v).X j) :
    inRight v i ≫ f ≫ (C v).d j l ≫ right v l =
      inRight v i ≫ f ≫ right v j ≫ A.d j l := by
  have hz : inRight v i ≫ f ≫ left v j=0 := hAB _ _ _
  have ht := congrArg (fun e => inRight v i ≫ f ≫ e) (total v j)
  simp only [comp_add,← Category.assoc,hz,zero_comp,zero_add,Category.comp_id] at ht
  have hf : inRight v i ≫ f = (inRight v i ≫ f ≫ right v j) ≫ inRight v j := ht.symm
  have hd : inRight v j ≫ (C v).d j l ≫ right v l=A.d j l := by
    rw [← Category.assoc,inRight_d,Category.assoc,inRight_right,Category.comp_id]
  calc
    inRight v i ≫ f ≫ (C v).d j l ≫ right v l =
        (inRight v i ≫ f) ≫ (C v).d j l ≫ right v l := by simp only [Category.assoc]
    _ = ((inRight v i ≫ f ≫ right v j) ≫ inRight v j) ≫
        (C v).d j l ≫ right v l := by rw [hf]
    _ = inRight v i ≫ f ≫ right v j ≫ A.d j l := by
      simp only [Category.assoc,hd]

include hAB in
theorem low_diff {a : ℤ} (f : Cochain (C v) (C v) a) :
    low v (diff (k:=k) f)=diff (k:=k) (low v f) := by
  funext i j h
  simp only [low,diff,comp_sub,sub_comp,Linear.comp_smul,Linear.smul_comp,Category.assoc]
  rw [low_post_d v hAB i (j+1) j]
  simp only [← Category.assoc,inRight_d]

/-- The actual cochain space, with the impossible fourth block removed. -/
def decomposition (a : ℤ) : Cochain (C v) (C v) a ≃ₗ[k]
    (Cochain A A a × Cochain B B a × Cochain B A (a-1)) where
  toFun f := (low v f, high v f, cross v f)
  invFun f := assemble v f.1 f.2.1 f.2.2
  left_inv f := assemble_blocks v hAB f
  right_inv f := by
    rcases f with ⟨f,g,c⟩
    simp only [low_assemble,high_assemble,cross_assemble]
  map_add' f g := by
    apply Prod.ext
    · change low v (f+g)=low v f+low v g
      funext i j h
      simp only [low,SignedDownHom.add_apply,comp_add,add_comp]
    · apply Prod.ext
      · change high v (f+g)=high v f+high v g
        funext i j h
        simp only [high,SignedDownHom.add_apply,comp_add,add_comp]
      · change cross v (f+g)=cross v f+cross v g
        funext i j h
        simp only [cross,SignedDownHom.add_apply,comp_add,add_comp]
  map_smul' t f := by
    apply Prod.ext
    · change low v (t • f)=t • low v f
      funext i j h
      simp only [low,SignedDownHom.smul_apply,Linear.comp_smul,Linear.smul_comp]
    · apply Prod.ext
      · change high v (t • f)=t • high v f
        funext i j h
        simp only [high,SignedDownHom.smul_apply,Linear.comp_smul,Linear.smul_comp]
      · change cross v (t • f)=t • cross v f
        funext i j h
        simp only [cross,SignedDownHom.smul_apply,Linear.comp_smul,Linear.smul_comp]

end
end TachikawaCharZero.SignedConeCochains
