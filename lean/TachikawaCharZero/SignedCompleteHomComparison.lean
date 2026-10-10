import TachikawaCharZero.SignedChainComparison
import OAI.RingTheory.Tachikawa.StableShift

/-! Evaluation of actual signed cochains at a complete augmentation.
The augmentation-lift and evaluation strategy adapt pinned OpenAI Math
DownHom.lean 410--532 (Apache-2.0, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). Signed boundaries retain
their scalar, and the converse uses the actual rephased nullhomotopy.
No characteristic-two cancellation or assumed Hom profile is used. -/
namespace TachikawaCharZero.SignedCompleteHomComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open OAI.Tachikawa SignedDownHom SignedRephasing SignedChainComparison
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}

theorem transport_left {a i i' j : ℤ} (f : Cochain P Q a) (h : i=i') (he : i'=j+a) :
    (P.XIsoOfEq h).hom ≫ f i' j he=f i j (h.trans he) := by
  subst i'
  simp

variable (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε=0)

def evalCycle {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f) :
    VectorSplit.Z (completeHom (k:=k) P N) a :=
  ⟨f a 0 (by omega) ≫ ε,by
    apply (completeHom_memZ P N a _).mpr
    have hc := rephase_comm f hf (a+1) 1 a 0 (by omega) (by omega) rfl
    rw [rephase_target_zero] at hc
    rw [← Category.assoc,← hc,Category.assoc,hε,comp_zero]⟩

def evalClass {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f) :
    VectorSplit.H (completeHom (k:=k) P N) a :=
  VectorSplit.quotient _ a (evalCycle ε hε f hf)

theorem eval_boundary {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f)
    (hb : Boundary (k:=k) f) : evalClass ε hε f hf=0 := by
  obtain ⟨c,hc⟩ := hb
  apply (VectorSplit.quotient_zero_iff_predecessor a _).mpr
  refine ⟨-sign (k:=k) (a-1) • (c (a-1) 0 (by omega) ≫ ε),?_⟩
  change P.d a (a-1) ≫ (-sign (k:=k) (a-1) • (c (a-1) 0 _ ≫ ε))=
    f a 0 _ ≫ ε
  have hr := congrArg (fun g => g a 0 (show a=0+a by omega)) hc
  dsimp only [diffAt] at hr
  rw [← hr,sub_comp,Linear.smul_comp,Category.assoc,
    show Q.d (0+1) 0 ≫ ε=0 from hε,comp_zero,zero_sub,
    ← neg_smul,Linear.comp_smul,Category.assoc]

variable (hP : TotallyAcyclic P) (hQ : ComplexExact Q)
  (pP : ∀ j, Module.Projective R (P.X j))
  (fP : ∀ j, Module.Finite R (P.X j))
  (fQ : ∀ j, Module.Finite R (Q.X j)) (pQ : ∀ j, Module.Projective R (Q.X j))
  (he : Function.Exact (Q.d 1 0) ε) (hs : Function.Surjective ε)

include hP hQ pP fP fQ pQ he hs in
theorem boundary_of_eval_zero {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f)
    (hz : evalClass ε hε f hf=0) : Boundary (k:=k) f := by
  obtain ⟨g,hg⟩ := (VectorSplit.quotient_zero_iff_predecessor a _).mp hz
  change P.X (a-1) ⟶ N at g
  change P.d a (a-1) ≫ g=f a 0 _ ≫ ε at hg
  let P' := SignedRephasing.translate P a
  let e := CokerAt.augmentationEquiv Q N 0 ε.hom he hs
  let g' : P'.X (-1) →ₗ[R] N :=
    g.hom.comp (P.XIsoOfEq (show -1+a=a-1 by omega)).hom.hom
  have hfac : CokerAt.map (toChain f hf) 0 ∈ projectiveFactors (k:=k) := by
    refine ⟨P'.X (-1),?_,?_,CokerAt.δ P' 0 (-1),e.symm.toLinearMap.comp g',?_⟩
    · exact fP (-1+a)
    · exact pP (-1+a)
    · apply LinearMap.ext
      intro x
      obtain ⟨y,rfl⟩ := CokerAt.π_surjective P' 0 x
      apply e.injective
      change e (e.symm (g' (P'.d 0 (-1) y)))=e (CokerAt.π Q 0 ((toChain f hf).f 0 y))
      rw [LinearEquiv.apply_symm_apply,toChain_target_zero]
      change g ((P.XIsoOfEq (show -1+a=a-1 by omega)).hom (P.d (0+a) (-1+a) y))=
        ε (f (0+a) 0 rfl y)
      have hm : P.d (0+a) (-1+a) ≫ (P.XIsoOfEq (show -1+a=a-1 by omega)).hom ≫ g=
          f (0+a) 0 rfl ≫ ε := by
        rw [← Category.assoc,P.d_comp_XIsoOfEq_hom]
        have hx := congrArg (fun z => (P.XIsoOfEq (show 0+a=a by omega)).hom ≫ z) hg
        rw [← Category.assoc,P.XIsoOfEq_hom_comp_d,← Category.assoc,transport_left] at hx
        exact hx
      exact congrArg (fun z => z y) hm
  obtain ⟨h⟩ := nullhomotopic_of_coker_factors (k:=k) (toChain f hf)
    (translate_totallyAcyclic P a hP) hQ (fun j => pP (j+a)) fQ pQ hfac
  exact homotopy_boundary f hf h

include hP hQ pP fP fQ pQ he hs in
theorem eval_zero_iff_boundary {a : ℤ} (f : Cochain P Q a) (hf : Closed (k:=k) f) :
    evalClass ε hε f hf=0 ↔ Boundary (k:=k) f :=
  ⟨boundary_of_eval_zero ε hε hP hQ pP fP fQ pQ he hs f hf,
    eval_boundary ε hε f hf⟩

include hP hQ pP fQ pQ he hs in
theorem exists_augmented_lift (g : P.X 0 ⟶ N) (hg : P.d 1 0 ≫ g=0) :
    ∃ u : P ⟶ Q, u.f 0 ≫ ε=g := by
  let e := CokerAt.augmentationEquiv Q N 0 ε.hom he hs
  let v := e.symm.toLinearMap.comp (CokerAt.descend P 0 g.hom (ModuleCat.hom_ext_iff.mp hg))
  obtain ⟨u,hu⟩ := exists_complete_lift P Q hP hQ pP fQ pQ v
  refine ⟨u,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hy := congrArg e (LinearMap.congr_fun hu (CokerAt.π P 0 y))
  change ε (u.f 0 y)=e (e.symm (g y)) at hy
  change ε (u.f 0 y)=g y
  simpa only [LinearEquiv.apply_symm_apply] using hy

include hP hQ pP fQ pQ he hs in
theorem eval_surjective (a : ℤ) (x : VectorSplit.H (completeHom (k:=k) P N) a) :
    ∃ (f : Cochain P Q a) (hf : Closed (k:=k) f), evalClass ε hε f hf=x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  let g : (SignedRephasing.translate P a).X 0 ⟶ N :=
    (P.XIsoOfEq (show 0+a=a by omega)).hom ≫ z.val
  have hg : (SignedRephasing.translate P a).d 1 0 ≫ g=0 := by
    dsimp only [g,SignedRephasing.translate]
    erw [← Category.assoc,P.d_comp_XIsoOfEq_hom]
    have hz := (completeHom_memZ P N a z.val).mp z.property
    have hx := congrArg (fun t => (P.XIsoOfEq (show 1+a=a+1 by omega)).hom ≫ t) hz
    erw [← Category.assoc,P.XIsoOfEq_hom_comp_d,comp_zero] at hx
    exact hx
  obtain ⟨u,hu⟩ := exists_augmented_lift ε (translate_totallyAcyclic P a hP)
    hQ (fun j => pP (j+a)) fQ pQ he hs g hg
  refine ⟨ofChain (k:=k) (P:=P) (a:=a) u,ofChain_closed u,?_⟩
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (phase (k:=k) a 0 • ((P.XIsoOfEq (show a=0+a by omega)).hom ≫ u.f 0)) ≫ ε=z.val
  rw [phase_zero,one_smul,Category.assoc,hu]
  dsimp only [g]
  erw [← Category.assoc]
  simp

end
end TachikawaCharZero.SignedCompleteHomComparison
