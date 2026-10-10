import OAI.RingTheory.Tachikawa.CompleteResolution
import Mathlib.Algebra.Homology.HomotopyCofiber

/-! Characteristic-independent signed cone excerpt from pinned OpenAI Math
(Apache-2.0). Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
variable {R : Type} [Ring R]
namespace CompleteCone
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
abbrev complex := HomologicalComplex.homotopyCofiber v
private lemma rel (j : ℤ) : (ComplexShape.down ℤ).Rel j (j-1) := by
  change j-1+1=j; omega
abbrev left (j : ℤ) : (complex v).X j ⟶ B.X (j-1) :=
  HomologicalComplex.homotopyCofiber.fstX v j (j-1) (rel j)
abbrev right (j : ℤ) : (complex v).X j ⟶ A.X j :=
  HomologicalComplex.homotopyCofiber.sndX v j
abbrev inLeft (j : ℤ) : B.X (j-1) ⟶ (complex v).X j :=
  HomologicalComplex.homotopyCofiber.inlX v (j-1) j (rel j)
abbrev inRight (j : ℤ) : A.X j ⟶ (complex v).X j :=
  HomologicalComplex.homotopyCofiber.inrX v j

@[simp] lemma inLeft_left (j : ℤ) : inLeft v j ≫ left v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.inlX_fstX
@[simp] lemma inLeft_right (j : ℤ) : inLeft v j ≫ right v j = 0 := by
  apply HomologicalComplex.homotopyCofiber.inlX_sndX
@[simp] lemma inRight_left (j : ℤ) : inRight v j ≫ left v j = 0 := by
  apply HomologicalComplex.homotopyCofiber.inrX_fstX
@[simp] lemma inRight_right (j : ℤ) : inRight v j ≫ right v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.inrX_sndX
lemma total (j : ℤ) : left v j ≫ inLeft v j + right v j ≫ inRight v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.ext_to_X v j (j-1) (rel j) <;>
    simp only [add_comp,Category.assoc,inLeft_left,inLeft_right,inRight_left,
      inRight_right,Category.comp_id,comp_zero,zero_add,add_zero,Category.id_comp]

lemma ext_element (j : ℤ) {x y : (complex v).X j}
    (hl : left v j x = left v j y) (hr : right v j x = right v j y) : x = y := by
  have hx := congrArg (fun f => f x) (total v j)
  have hy := congrArg (fun f => f y) (total v j)
  change inLeft v j (left v j x) + inRight v j (right v j x) = x at hx
  change inLeft v j (left v j y) + inRight v j (right v j y) = y at hy
  rw [hl,hr,hy] at hx
  exact hx.symm

lemma left_d (j : ℤ) (x : (complex v).X j) :
    left v (j-1) ((complex v).d j (j-1) x) = - B.d (j-1) (j-1-1) (left v j x) := by
  exact congrArg (fun f => f x)
    (HomologicalComplex.homotopyCofiber.d_fstX v j (j-1) (j-1-1) (rel j) (rel (j-1)))
lemma right_d (j : ℤ) (x : (complex v).X j) :
    right v (j-1) ((complex v).d j (j-1) x) =
      v.f (j-1) (left v j x) + A.d j (j-1) (right v j x) := by
  exact congrArg (fun f => f x)
    (HomologicalComplex.homotopyCofiber.d_sndX v j (j-1) (rel j))
lemma inRight_d (i j : ℤ) : inRight v i ≫ (complex v).d i j = A.d i j ≫ inRight v j :=
  HomologicalComplex.homotopyCofiber.inrX_d v i j
lemma inLeft_d (j : ℤ) : inLeft v j ≫ (complex v).d j (j-1) =
    -B.d (j-1) (j-1-1) ≫ inLeft v (j-1) + v.f (j-1) ≫ inRight v (j-1) :=
  HomologicalComplex.homotopyCofiber.inlX_d v j (j-1) (j-1-1) (rel j) (rel (j-1))

lemma exact (hA : ComplexExact A) (hB : ComplexExact B) : ComplexExact (complex v) := by
  intro j x
  constructor
  · intro hx
    have hl : B.d (j-1) (j-1-1) (left v j x) = 0 := by
      have he := left_d v j x
      rw [hx,map_zero] at he
      exact neg_eq_zero.mp he.symm
    have hex := hB (j-1)
    rw [show j-1+1=j by omega] at hex
    obtain ⟨b,hb⟩ := (hex _).mp hl
    let y : (complex v).X (j+1) :=
      HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) (-b)
    have hyl : left v j ((complex v).d (j+1) j y) = left v j x := by
      have he : HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) ≫
          (complex v).d (j+1) j ≫ left v j = -B.d j (j-1) := by
        calc
          _ = (-B.d j (j-1) ≫ inLeft v j + v.f j ≫ inRight v j) ≫ left v j :=
            (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ left v j)
              (HomologicalComplex.homotopyCofiber.inlX_d v (j+1) j (j-1) (by rfl) (rel j)))
          _ = _ := by simp only [add_comp,neg_comp,Category.assoc,inLeft_left,inRight_left,
            Category.comp_id,comp_zero,add_zero]
      have he' := congrArg (fun f => f (-b)) he
      change left v j ((complex v).d (j+1) j y) = -(B.d j (j-1) (-b)) at he'
      rw [map_neg,neg_neg] at he'
      exact he'.trans hb
    let z := x - (complex v).d (j+1) j y
    have hzl : left v j z = 0 := by simp only [z,map_sub,hyl,sub_self]
    have hzd : (complex v).d j (j-1) z = 0 := by
      rw [map_sub,hx]
      have hd := congrArg (fun f => f y) ((complex v).d_comp_d (j+1) j (j-1))
      change (complex v).d j (j-1) ((complex v).d (j+1) j y) = 0 at hd
      rw [hd,sub_self]
    have hzr : A.d j (j-1) (right v j z) = 0 := by
      have he := right_d v j z
      rw [hzd,map_zero,hzl,map_zero,zero_add] at he
      exact he.symm
    obtain ⟨a,ha⟩ := (hA j _).mp hzr
    refine ⟨y + inRight v (j+1) a,?_⟩
    rw [map_add]
    have hd := congrArg (fun f => f a) (inRight_d v (j+1) j)
    change (complex v).d (j+1) j (inRight v (j+1) a) = inRight v j (A.d (j+1) j a) at hd
    rw [hd,ha]
    have hz : inRight v j (right v j z) = z := by
      apply ext_element v j
      · exact (congrArg (fun f => f (right v j z)) (inRight_left v j)).trans hzl.symm
      · exact congrArg (fun f => f (right v j z)) (inRight_right v j)
    rw [hz]
    dsimp only [z]
    rw [add_comm,sub_add_cancel]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) ((complex v).d_comp_d (j+1) j (j-1))

private lemma boundaries {P : ChainComplex (ModuleCat.{0} R) ℤ} (hP : TotallyAcyclic P)
    (j : ℤ) (f : P.X j ⟶ ModuleCat.of R R) (hf : P.d (j+1) j ≫ f = 0) :
    ∃ g : P.X (j-1) ⟶ ModuleCat.of R R, P.d j (j-1) ≫ g = f := by
  obtain ⟨g,hg⟩ := hP.2 j f.hom (ModuleCat.hom_ext_iff.mp hf)
  exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩

lemma totallyAcyclic (hA : TotallyAcyclic A) (hB : TotallyAcyclic B) :
    TotallyAcyclic (complex v) := by
  refine ⟨exact v hA.1 hB.1,?_⟩
  intro j fl hfl
  let f : (complex v).X j ⟶ ModuleCat.of R R := ModuleCat.ofHom fl
  have hf : (complex v).d (j+1) j ≫ f = 0 := ModuleCat.hom_ext hfl
  have hfa : A.d (j+1) j ≫ (inRight v j ≫ f) = 0 := by
    rw [← Category.assoc,← inRight_d,Category.assoc,hf,comp_zero]
  obtain ⟨a,ha⟩ := boundaries hA j (inRight v j ≫ f) hfa
  let t := f - (complex v).d j (j-1) ≫ right v (j-1) ≫ a
  have htr : inRight v j ≫ t = 0 := by
    dsimp only [t]
    rw [comp_sub,← Category.assoc,← Category.assoc,inRight_d]
    simp only [Category.assoc]
    rw [← Category.assoc (inRight v (j-1)) (right v (j-1)) a,
      inRight_right,Category.id_comp,ha,sub_self]
  have htcy : (complex v).d (j+1) j ≫ t = 0 := by
    dsimp only [t]
    rw [comp_sub,hf,← Category.assoc,← Category.assoc,
      (complex v).d_comp_d,zero_comp,zero_comp,sub_self]
  let b := inLeft v j ≫ t
  have htb : t = left v j ≫ b := by
    calc
      t = (left v j ≫ inLeft v j + right v j ≫ inRight v j) ≫ t := by rw [total,Category.id_comp]
      _ = _ := by rw [add_comp,Category.assoc,Category.assoc,htr,comp_zero,add_zero]
  have hbcy : B.d j (j-1) ≫ b = 0 := by
    have he := congrArg (fun h => h ≫ t)
      (HomologicalComplex.homotopyCofiber.inlX_d v (j+1) j (j-1) (by rfl) (rel j))
    change (HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) ≫
      (complex v).d (j+1) j) ≫ t =
      (-B.d j (j-1) ≫ inLeft v j + v.f j ≫ inRight v j) ≫ t at he
    simp only [Category.assoc,htcy,comp_zero,add_comp,neg_comp,htr,add_zero] at he
    exact neg_eq_zero.mp he.symm
  have hbound := boundaries hB (j-1)
  rw [show j-1+1=j by omega] at hbound
  obtain ⟨b',hb'⟩ := hbound b hbcy
  let g := right v (j-1) ≫ a - left v (j-1) ≫ b'
  have hg : (complex v).d j (j-1) ≫ g = f := by
    dsimp only [g]
    rw [comp_sub]
    have hd : (complex v).d j (j-1) ≫ left v (j-1) = -left v j ≫ B.d (j-1) (j-1-1) :=
      HomologicalComplex.homotopyCofiber.d_fstX v j (j-1) (j-1-1) (rel j) (rel (j-1))
    rw [← Category.assoc ( (complex v).d j (j-1)) (left v (j-1)) b',hd,
      neg_comp,Category.assoc,hb',← htb,sub_neg_eq_add]
    dsimp only [t]
    rw [add_comm,sub_add_cancel]
  exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩

def termEquiv (j : ℤ) : (complex v).X j ≃ₗ[R] (B.X (j-1) × A.X j) :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod v j (j-1) (rel j) ≪≫
    ModuleCat.biprodIsoProd (B.X (j-1)) (A.X j)).toLinearEquiv

lemma finite (af : ∀ j, Module.Finite R (A.X j)) (bf : ∀ j, Module.Finite R (B.X j))
    (j : ℤ) : Module.Finite R ((complex v).X j) := by
  let := af j
  let := bf (j-1)
  exact Module.Finite.equiv (termEquiv v j).symm
lemma projective (ap : ∀ j, Module.Projective R (A.X j))
    (bp : ∀ j, Module.Projective R (B.X j)) (j : ℤ) :
    Module.Projective R ((complex v).X j) := by
  let := ap j
  let := bp (j-1)
  exact Module.Projective.of_equiv (termEquiv v j).symm

end CompleteCone

end Tachikawa
end
end OAI
