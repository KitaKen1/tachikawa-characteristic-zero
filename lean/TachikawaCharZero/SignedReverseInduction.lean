import TachikawaCharZero.ReverseHom
import OAI.RingTheory.Tachikawa.InductionQuasiIso

/-! The actual rational signed reverse comparison remains a quasi-isomorphism
after Nakayama and after induction to the symmetric trivial extension. -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
open TachikawaCharZero.Resolution
open OAI.Tachikawa (Nakayama)
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

theorem nu_initial_surjective : Function.Surjective
    (OAI.Tachikawa.Nakayama.map (k:=ℚ) initialMap) :=
  LinearMap.dualMap_surjective_of_injective
    (f := homInitial.restrictScalars ℚ) homInitial_injective

theorem nu_resD_exact (n : ℕ) (hn : n≠1) : Function.Exact
    (OAI.Tachikawa.Nakayama.map (k:=ℚ) (resD (n+1)).hom)
    (OAI.Tachikawa.Nakayama.map (resD n).hom) := by
  rcases n with _ | _ | m
  · exact OAI.Tachikawa.exact_dual (homInitial.restrictScalars ℚ)
      ((homDiff 1).restrictScalars ℚ) homInitial_exact
  · exact (hn rfl).elim
  · exact OAI.Tachikawa.exact_dual ((homDiff ((-2:ℚ)^(m+1))).restrictScalars ℚ)
      ((homDiff ((-2:ℚ)^(m+2))).restrictScalars ℚ) (homDiff_exact_all_degrees m)

theorem nuForward_exactAt (j : ℤ) (hj : j≠2) :
    (OAI.Tachikawa.Nakayama.complex (k:=ℚ) forwardComplex).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j=i+1 := ⟨j-1,by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, OAI.Tachikawa.Nakayama.map
    (ChainComplex.of.d _ forwardD (i+1) i).hom x=0 →
    ∃ y, OAI.Tachikawa.Nakayama.map
      (ChainComplex.of.d _ forwardD (i+1+1) (i+1)).hom y=x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n =>
    exact fun x hx => (nu_resD_exact n (by intro hn; subst n; exact hj rfl) x).mp hx
  | negSucc n =>
    cases n with
    | zero => exact fun x _ => nu_initial_surjective x
    | succ n =>
      intro x _
      exact ⟨0,@Subsingleton.elim ((PUnit →ₗ[A] A) →ₗ[ℚ] ℚ) inferInstance _ _⟩

theorem nuReverse_exactAt (j : ℤ) (hj : j≠2) :
    (OAI.Tachikawa.Nakayama.complex (k:=ℚ) reverseComplex).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j=i+1 := ⟨j-1,by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, OAI.Tachikawa.Nakayama.map
    (ChainComplex.of.d _ reverseD (i+1) i).hom x=0 →
    ∃ y, OAI.Tachikawa.Nakayama.map
      (ChainComplex.of.d _ reverseD (i+1+1) (i+1)).hom y=x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n =>
    rcases n with _ | _ | n
    · exact fun x hx => (nu_reverse_top_exact x).mp hx
    · exact (hj rfl).elim
    · intro x _
      exact ⟨0,@Subsingleton.elim ((PUnit →ₗ[A] A) →ₗ[ℚ] ℚ) inferInstance _ _⟩
  | negSucc n =>
    rcases n with _ | _ | n
    · exact fun x hx => (nu_reverse_exact 0 x).mp hx
    · exact fun x hx => (nu_reverse_exact 1 x).mp hx
    · exact fun x hx => (nu_reverse_exact (n+2) x).mp hx

def nuComparison :=
  ((OAI.Tachikawa.Nakayama.functor (k:=ℚ)).mapHomologicalComplex
    (ComplexShape.down ℤ)).map reverseComparison

theorem nuComparison_quasiIso : QuasiIso nuComparison := by
  constructor
  intro j
  by_cases hj : j=2
  · subst j
    rw [quasiIsoAt_iff' _ 3 2 1 (by simp) (by simp)]
    apply OAI.Tachikawa.shortComplex_quasiIso_of_cycles
    · intro x hx hb
      obtain ⟨z,hz⟩ := hb
      change OAI.Tachikawa.Nakayama.map (ceDiff ((-2:ℚ)^0)) x=0 at hx
      rw [pow_zero] at hx
      have hV : OAI.Tachikawa.Nakayama.map rhoV x=0 := by
        change OAI.Tachikawa.Nakayama.map (0 : PUnit →ₗ[A] Cf) z=
          OAI.Tachikawa.Nakayama.map rhoV x at hz
        erw [OAI.Tachikawa.Nakayama.map_zero,LinearMap.zero_apply] at hz
        exact hz.symm
      obtain ⟨ξ,hξ⟩ := nuV_cycles_injective x hx hV
      refine ⟨ξ, ?_⟩
      change OAI.Tachikawa.Nakayama.map (ceDiff ((-2:ℚ)^1)) ξ=x
      simpa only [pow_one] using hξ
    · intro y hy
      obtain ⟨x,hx,hV⟩ := nuV_cycles_surjective y hy
      refine ⟨x, ?_,0, ?_⟩
      · change OAI.Tachikawa.Nakayama.map (ceDiff ((-2:ℚ)^0)) x=0
        simpa only [pow_zero] using hx
      · change OAI.Tachikawa.Nakayama.map (0 : PUnit →ₗ[A] Cf) 0=
          OAI.Tachikawa.Nakayama.map rhoV x-(show Nakayama ℚ A Cf from y)
        erw [map_zero,hV,sub_self]
  · exact (quasiIsoAt_iff_exactAt _ j (nuForward_exactAt j hj)).mpr
      (nuReverse_exactAt j hj)

def inducedForward :=
  ((OAI.Tachikawa.TrivialInduction.functor (k:=ℚ)).mapHomologicalComplex
    (ComplexShape.down ℤ)).obj forwardComplex

def inducedReverse :=
  ((OAI.Tachikawa.TrivialInduction.functor (k:=ℚ)).mapHomologicalComplex
    (ComplexShape.down ℤ)).obj reverseComplex

def inducedComparison : inducedForward ⟶ inducedReverse :=
  ((OAI.Tachikawa.TrivialInduction.functor (k:=ℚ)).mapHomologicalComplex
    (ComplexShape.down ℤ)).map reverseComparison

theorem inducedComparison_quasiIso : QuasiIso inducedComparison :=
  OAI.Tachikawa.TrivialInduction.quasiIso_map _ reverseComparison_quasiIso
    nuComparison_quasiIso

theorem inducedForward_term_projective (j : ℤ) : Projective (inducedForward.X j) := by
  let := forward_term_finiteA j
  let := forward_term_projective j
  let : Module.Projective A (forwardComplex.X j) := inferInstance
  change Projective (ModuleCat.of (OAI.Tachikawa.TrivialExtension ℚ A)
    (OAI.Tachikawa.TrivialInduction.Obj ℚ A (forwardComplex.X j)))
  infer_instance

theorem inducedReverse_term_projective (j : ℤ) : Projective (inducedReverse.X j) := by
  let := reverse_term_finiteA j
  let := reverse_term_projective j
  let : Module.Projective A (reverseComplex.X j) := inferInstance
  change Projective (ModuleCat.of (OAI.Tachikawa.TrivialExtension ℚ A)
    (OAI.Tachikawa.TrivialInduction.Obj ℚ A (reverseComplex.X j)))
  infer_instance

theorem inducedForward_term_finite (j : ℤ) : Module.Finite ℚ (inducedForward.X j) := by
  let := forward_term_finite j
  have hf : Module.Finite (OAI.Tachikawa.TrivialExtension ℚ A) (inducedForward.X j) :=
    Module.Finite.of_restrictScalars_finite ℚ (OAI.Tachikawa.TrivialExtension ℚ A)
      (OAI.Tachikawa.TrivialInduction.Obj ℚ A (forwardComplex.X j))
  exact Module.Finite.trans (OAI.Tachikawa.TrivialExtension ℚ A) _

theorem inducedReverse_term_finite (j : ℤ) : Module.Finite ℚ (inducedReverse.X j) := by
  let := reverse_term_finite j
  have hf : Module.Finite (OAI.Tachikawa.TrivialExtension ℚ A) (inducedReverse.X j) :=
    Module.Finite.of_restrictScalars_finite ℚ (OAI.Tachikawa.TrivialExtension ℚ A)
      (OAI.Tachikawa.TrivialInduction.Obj ℚ A (reverseComplex.X j))
  exact Module.Finite.trans (OAI.Tachikawa.TrivialExtension ℚ A) _

end
end TachikawaCharZero.ReverseCorner
