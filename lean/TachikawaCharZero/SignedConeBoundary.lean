import TachikawaCharZero.SignedConeDifferential

/-! A characteristic-independent signed boundary criterion for the actual
cone cochains. The two connecting-map inputs are explicit hypotheses;
their comparison with actual complete-Hom Delta is a separate obligation.
The block-elimination strategy adapts pinned OpenAI Math Cone.lean
373--462 (fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0).
Here subtraction and the negative high differential replace all uses of
characteristic-two cancellation. -/
namespace TachikawaCharZero.SignedConeBoundary
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open OAI.Tachikawa.CompleteCone SignedDownHom SignedConeCochains SignedConeDifferential
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

theorem low_zero (a : ℤ) : low v (0 : Cochain (C v) (C v) a)=0 := by
  funext i j h
  simp only [low,SignedDownHom.zero_apply,comp_zero,zero_comp]
theorem high_zero (a : ℤ) : high v (0 : Cochain (C v) (C v) a)=0 := by
  funext i j h
  simp only [high,SignedDownHom.zero_apply,comp_zero,zero_comp]
theorem cross_zero (a : ℤ) : cross v (0 : Cochain (C v) (C v) a)=0 := by
  funext i j h
  simp only [cross,SignedDownHom.zero_apply,comp_zero,zero_comp]

theorem low_sub {a : ℤ} (f g : Cochain (C v) (C v) a) :
    low v (f-g)=low v f-low v g := by
  funext i j h
  simp only [low,SignedDownHom.sub_apply,comp_sub,sub_comp]
theorem high_sub {a : ℤ} (f g : Cochain (C v) (C v) a) :
    high v (f-g)=high v f-high v g := by
  funext i j h
  simp only [high,SignedDownHom.sub_apply,comp_sub,sub_comp]

theorem connecting_zero (a : ℤ) :
    connecting (k:=k) v (0 : Cochain A A a) (0 : Cochain B B a)=0 := by
  funext i j h
  simp only [connecting,SignedDownHom.sub_apply,SignedDownHom.smul_apply,
    pre,post,SignedDownHom.zero_apply,comp_zero,zero_comp,smul_zero,sub_zero]

variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB in
theorem blocks_ext {a : ℤ} {f g : Cochain (C v) (C v) a}
    (hl : low v f=low v g) (hh : high v f=high v g) (hc : cross v f=cross v g) : f=g := by
  rw [← assemble_blocks v hAB f,← assemble_blocks v hAB g,hl,hh,hc]

include hAB in
theorem closed_blocksAt {a : ℤ} (f : Cochain (C v) (C v) (a-1))
    (hf : Closed (k:=k) f) :
    Closed (k:=k) (low v f) ∧ Closed (k:=k) (high v f) ∧
      connecting (k:=k) v (low v f) (high v f)= -diffAt (k:=k) (cross v f) := by
  have hz := (closed_iff_diffAt f).mp hf
  refine ⟨(closed_iff_diffAt _).mpr ?_,(closed_iff_diffAt _).mpr ?_,?_⟩
  · rw [← low_diffAt v hAB,hz,low_zero]
  · have hh := congrArg (high v) hz
    rw [high_diffAt v hAB,high_zero] at hh
    exact neg_eq_zero.mp hh
  · have hc := congrArg (cross v) hz
    rw [cross_diffAt v hAB,cross_zero] at hc
    have he : diffAt (k:=k) (cross v f)+connecting (k:=k) v (low v f) (high v f)=0 := by
      simpa only [connecting,add_sub_assoc] using hc
    exact eq_neg_of_add_eq_zero_right he

include hAB in
theorem closed_blocks {a : ℤ} (f : Cochain (C v) (C v) a)
    (hf : Closed (k:=k) f) :
    Closed (k:=k) (low v f) ∧ Closed (k:=k) (high v f) ∧
      connecting (k:=k) v (low v f) (high v f)= -diffAt (k:=k) (cross v f) := by
  have hh := closed_blocksAt (k:=k) v hAB (a:=a+1)
  rw [show a+1-1=a by omega] at hh
  exact hh f hf

include hAB in
/-- Injectivity in degree a and surjectivity in degree a-1 at the level
of closed cochains modulo actual signed boundaries imply the desired
cone boundary. No dimensional surrogate or characteristic assumption. -/
theorem boundary_of_connecting (a : ℤ)
    (hI : ∀ (f : Cochain A A a) (g : Cochain B B a),
      Closed (k:=k) f → Closed (k:=k) g →
      Boundary (k:=k) (connecting (k:=k) v f g) →
      Boundary (k:=k) f ∧ Boundary (k:=k) g)
    (hS : ∀ (c : Cochain B A (a-1)), Closed (k:=k) c →
      ∃ (f : Cochain A A (a-1)) (g : Cochain B B (a-1)),
        Closed (k:=k) f ∧ Closed (k:=k) g ∧
        Boundary (k:=k) (c-connecting (k:=k) v f g))
    (z : Cochain (C v) (C v) a) (hz : Closed (k:=k) z) : Boundary (k:=k) z := by
  obtain ⟨hf,hg,he⟩ := closed_blocks v hAB z hz
  have hb : Boundary (k:=k) (connecting (k:=k) v (low v z) (high v z)) := by
    rw [he]
    exact boundary_neg (boundary_diffAt _)
  obtain ⟨⟨s,hs⟩,⟨t,ht⟩⟩ := hI _ _ hf hg hb
  let b := diffAt (k:=k) (assemble v s (-t) 0)
  let zz := z-b
  have hzz : Closed (k:=k) zz := closed_sub hz (closed_diffAt _)
  have hl : low v zz=0 := by
    dsimp only [zz,b]
    rw [low_sub,low_diffAt v hAB,low_assemble,hs,sub_self]
  have hh : high v zz=0 := by
    dsimp only [zz,b]
    rw [high_sub,high_diffAt v hAB,high_assemble,diffAt_neg,neg_neg,ht,sub_self]
  have hcc : Closed (k:=k) (cross v zz) := by
    apply (closed_iff_diffAt _).mpr
    have hc := (closed_blocks v hAB zz hzz).2.2
    rw [hl,hh,connecting_zero] at hc
    exact neg_eq_zero.mp hc.symm
  obtain ⟨f,g,hf,hg,⟨c,hc⟩⟩ := hS (cross v zz) hcc
  have hf0 := (closed_iff_diffAt f).mp hf
  have hg0 := (closed_iff_diffAt g).mp hg
  have hd : diffAt (k:=k) (assemble v f g c)=zz := by
    apply blocks_ext v hAB
    · rw [low_diffAt v hAB,low_assemble,hf0,hl]
    · rw [high_diffAt v hAB,high_assemble,hg0,neg_zero,hh]
    · rw [cross_diffAt v hAB,cross_assemble,low_assemble,high_assemble,hc]
      simp only [connecting]
      abel
  have hzB : Boundary (k:=k) zz := ⟨assemble v f g c,hd⟩
  have hbB : Boundary (k:=k) b := boundary_diffAt _
  have hsum : zz+b=z := sub_add_cancel z b
  rw [← hsum]
  exact boundary_add hzB hbB

end
end TachikawaCharZero.SignedConeBoundary
