import TachikawaCharZero.InducedComplex

/-! Degree two of the induced complex is the actual T-character module.
The evaluation at v is T-linear, including the square-zero dual action;
the first coordinate of a cycle kills v and its dual coordinate kills z.
No tensor-evaluation or derived-category comparison is assumed. -/
namespace TachikawaCharZero.Induced
noncomputable section
open Resolution CategoryTheory CategoryTheory.Limits OAI.ArExplicit

def v : EC := ecIso ![0,0,0,0,0,1]
def z : EC := ecIso ![0,0,0,1,0,0]
abbrev Cycles := LinearMap.ker (teDiff 1)

theorem leftDiff_v (t : ℚ) : leftDiff t v=0 := by
  rw [v,leftDiff_iso,← ecIso.map_zero]
  congr 1
  ext i
  fin_cases i <;> simp [leftD]

theorem cycle_first_e (a : Cycles) : (a.val:T).fst.coeff .e=0 := by
  have h := congrArg (fun x : TE => (x:T).fst.coeff .x) a.property
  change ((a.val:T).fst*ell 1).coeff .x=0 at h
  simpa [ell,BaseAlgebra.product] using h

theorem cycle_snd_z (a : Cycles) : (a.val:T).snd (z:A)=0 := by
  let b : A := (1/2:ℚ) • BaseAlgebra.basisVector 2 .y
  have hb : ell 1*b=(z:A) := by
    ext i
    cases i <;> norm_num [b,ell,z,ecIso,ecEmbed,BaseAlgebra.product]
  have h := congrArg (fun x : TE => (x:T).snd b) a.property
  change (((a.val:T).fst • (0:Dual) + MulOpposite.op (ell 1) • (a.val:T).snd) b)=0 at h
  simpa only [smul_zero,zero_add,dual_right_apply,MulOpposite.unop_op,hb] using h

theorem cycle_mul_v (a : Cycles) : (a.val:T).fst*(v:A)=0 := by
  ext i
  cases i <;> simp [v,ecIso,ecEmbed,BaseAlgebra.product,cycle_first_e a]

theorem v_mul (a : A) : (v:A)*a=a.coeff .f • (v:A)+(2*a.coeff .t) • (z:A) := by
  ext i
  cases i <;> simp [v,z,ecIso,ecEmbed,BaseAlgebra.product]

def twoAug : Cycles →ₗ[T] S where
  toFun a := (a.val:T).snd (v:A)
  map_add' _ _ := rfl
  map_smul' a c := by
    change (a.fst • (c.val:T).snd + MulOpposite.op (c.val:T).fst • a.snd) (v:A)=
      a.fst.coeff .f*(c.val:T).snd (v:A)
    rw [dual_add_apply,dual_left_apply,dual_right_apply,MulOpposite.unop_op,
      cycle_mul_v,map_zero,v_mul]
    change (c.val:T).snd (a.fst.coeff .f • (v:A)+(2*a.fst.coeff .t) • (z:A))+0=_
    rw [map_add,map_smul,map_smul,cycle_snd_z]
    simp

def vFunctional : Module.Dual ℚ EC where
  toFun a := (a:A).coeff .v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vFunctional_closed : nuDiff 1 vFunctional=0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨b,rfl⟩ := ecIso.surjective a
  change (leftDiff 1 (ecIso b):A).coeff .v=0
  rw [leftDiff_iso]
  simp [ecIso,ecEmbed,leftD]

def cycleOne : Cycles := ⟨decompE.symm (0,vFunctional),by
  apply decompE.injective
  rw [teDiff_decomp,decompE.apply_symm_apply,map_zero,vFunctional_closed]
  rfl⟩

theorem cycleOne_aug : twoAug cycleOne=(1:ℚ) := by
  change (decompE (decompE.symm (0,vFunctional))).2 v=1
  rw [decompE.apply_symm_apply]
  rfl

theorem twoAug_surjective : Function.Surjective twoAug := by
  intro x
  refine ⟨(show ℚ from x) • cycleOne,?_⟩
  rw [LinearMap.map_smul_of_tower,cycleOne_aug]
  change (show ℚ from x)*1=(show ℚ from x)
  exact mul_one _

def boundary : TE →ₗ[T] Cycles := (teDiff (-2)).codRestrict _ (fun a => by
  change teDiff 1 (teDiff (-2) a)=0
  simpa using teDiff_sq 1 a)

theorem right_cycle_decompose (a : DualTwoCycles) :
    a.val=leftDiff 1 (ecIso ![(a.val:A).coeff .x,0,(a.val:A).coeff .z/2,0,0,0])+
      (a.val:A).coeff .v • v := by
  obtain ⟨h0,h2,h4⟩ := dualTwo_coordinates a
  rw [leftDiff_iso]
  apply ecIso.symm.injective
  rw [map_add,map_smul,ecIso.symm_apply_apply]
  change ecIso.symm a.val=leftD 1 _+(a.val:A).coeff .v • ![0,0,0,0,0,1]
  ext i
  fin_cases i <;> simp [ecIso,leftD,h0,h2,h4]
  ring

theorem twoAug_exact : Function.Exact boundary twoAug := by
  intro a
  constructor
  · intro ha
    have hc := congrArg decompE a.property
    rw [teDiff_decomp,map_zero] at hc
    have hc₁ : ceDiff 1 (decompE a.val).1=0 := congrArg Prod.fst hc
    have hc₂ : nuDiff 1 (decompE a.val).2=0 := congrArg Prod.snd hc
    obtain ⟨b,hb⟩ := (ceDiff_exact_all_degrees 0 _).mp hc₁
    let ψ := (decompE a.val).2
    have hv : ψ v=0 := ha
    have hr : ψ ∈ LinearMap.range ((leftDiff (-2)).restrictScalars ℚ).dualMap := by
      rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
      rw [Submodule.mem_dualAnnihilator]
      intro c hc
      let c' : DualTwoCycles := ⟨c,hc⟩
      change ψ c'.val=0
      rw [right_cycle_decompose c',map_add,map_smul]
      have hψ (w : EC) : ψ (leftDiff 1 w)=0 := LinearMap.congr_fun hc₂ w
      rw [hψ,hv,smul_zero,add_zero]
    obtain ⟨φ,hφ⟩ := hr
    refine ⟨decompE.symm (b,φ),?_⟩
    apply Subtype.ext
    apply decompE.injective
    change decompE (teDiff (-2) (decompE.symm (b,φ)))=decompE a.val
    rw [teDiff_decomp,decompE.apply_symm_apply]
    exact Prod.ext hb hφ
  · rintro ⟨b,rfl⟩
    change (decompE (teDiff (-2) b)).2 v=0
    rw [teDiff_decomp]
    change (decompE b).2 (leftDiff (-2) v)=0
    rw [leftDiff_v,map_zero]

local instance : HasQuotient Cycles (Submodule T Cycles) :=
  @Submodule.hasQuotient T Cycles inferInstance inferInstance inferInstance

def twoCohomologyEquiv : (Cycles ⧸ LinearMap.range boundary) ≃ₗ[T] S :=
  (Submodule.quotEquivOfEq _ _ twoAug_exact.linearMap_ker_eq.symm).trans
    (twoAug.quotKerEquivOfSurjective twoAug_surjective)

def twoShortComplex : ShortComplex (ModuleCat T) :=
  ShortComplex.moduleCatMk (teDiff (-2)) (teDiff 1) (by
    apply LinearMap.ext; intro a; simpa using teDiff_sq 1 a)

def twoHomologyIso : twoShortComplex.homology ≅ ModuleCat.of T S :=
  twoShortComplex.moduleCatHomologyIso ≪≫ twoCohomologyEquiv.toModuleIso

theorem complex_exactAt (n : ℕ) (hn₀ : n≠0) (hn₂ : n≠2) : complex.ExactAt n := by
  cases n with
  | zero => exact (hn₀ rfl).elim
  | succ n =>
    rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    change ∀ x : obj (n+1), complex.d (n+1) n x=0 → ∃ y, complex.d (n+2) (n+1) y=x
    rw [show complex.d (n+1) n=d n from ChainComplex.of_d _ _ _,
      show complex.d (n+2) (n+1)=d (n+1) from ChainComplex.of_d _ _ _]
    exact fun x => (d_exact n (by omega) x).mp

theorem complex_homology_zero (n : ℕ) (hn₀ : n≠0) (hn₂ : n≠2) :
    IsZero (complex.homology n) := (complex_exactAt n hn₀ hn₂).isZero_homology

def complexTwoIso : complex.sc' 3 2 1 ≅ twoShortComplex :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro a; rfl)
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro a; rfl)

def complex_homology_two : complex.homology 2 ≅ ModuleCat.of T S :=
  complex.homologyIsoSc' 3 2 1 (by simp) (by simp) ≪≫
    (ShortComplex.homologyFunctor (ModuleCat T)).mapIso complexTwoIso ≪≫ twoHomologyIso

end
end TachikawaCharZero.Induced
